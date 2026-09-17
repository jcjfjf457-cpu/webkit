/* 
Shared worker-RPC and thread-attribute helpers.
Two chains (lapse.js, netctrl.js) each grew an identical message-based RPC
shim over src/worker.js, and each grew its own save/pin/restore of the main
thread's cpuset affinity and realtime priority. The RPC in netctrl is the
superset (it labels timeouts/errors with a worker name and supports a
per-call timeoutMs where 0 means "no timeout"); that shape is lifted here
with lapse's 15000ms default. The thread-attr save/restore is the same four
syscalls in both chains (cpuset_getaffinity / rtprio_thread(RTP_LOOKUP) to
save, cpuset_setaffinity / rtprio_thread(RTP_SET) to restore); only the
buffer plumbing and the choice of pinned core differ per chain, so those
stay in the callers -- the helpers below take the buffers and an sc() as
parameters and return raw results, no logging, no policy.
*/
import { int64 } from "./int64.js";

export const DEFAULT_RPC_TIMEOUT_MS = 15000;

const THREAD_ATTR_MASK_SIZE = 0x10;
// FreeBSD: CPU_LEVEL_WHICH=3, CPU_WHICH_TID=1 (per-thread), RTP_LOOKUP=0.
export const CPU_LEVEL_WHICH = 3;
export const CPU_WHICH_TID = 1;
export const RTP_LOOKUP = 0;
export const RTP_SET = 1;

const THREAD_ID_ALL = () => new int64(0xffffffff, 0xffffffff);

/*
makeRpc: wrap a Worker whose global onmessage dispatches {id, type, value}
replies into promise-returning calls: rpc(name, timeoutMs, ...args).
timeoutMs === 0 means wait forever. Netctrl's shape, lapse's 15s default.
*/
export function makeRpc(w, name, defaultTimeoutMs, onError) {
    const DEFAULT_TIMEOUT = defaultTimeoutMs === undefined ? 15000 : defaultTimeoutMs;
    let seq = 0;
    const pending = new Map();
    w.onmessage = function (e) {
        const d = e.data || {};
        const slot = pending.get(d.id);
        if (!slot) return;
        pending.delete(d.id);
        if (slot.timer) clearTimeout(slot.timer);
        if (d.type === "err") slot.reject(new Error(String(d.value)));
        else slot.resolve(d.value);
    };
    /* 
    Both chains log worker crashes rather than throwing -- an unhandled
    throw in an error handler just lands in the console with no context.
    */
    w.onerror = e => {
        if (onError) onError(name, (e && e.message) ? e.message : String(e));
    };

    return function call(fname, timeoutMs, ...args) {
        return new Promise(function (resolve, reject) {
            const id = seq++;
            const effective = timeoutMs === undefined ? DEFAULT_TIMEOUT : timeoutMs;
            const timer = effective > 0 ? setTimeout(function () {
                pending.delete(id);
                reject(new Error((name || "worker") + ": timeout waiting for " + fname));
            }, effective) : null;
            pending.set(id, { resolve, reject, timer });
            w.postMessage({ id: id, name: fname, args: args });
        });
    };
}

/*
Syscall numbers differ per chain (they come from each chain's SYS/stub
table), so every helper takes them as { cpuset_getaffinity,
cpuset_setaffinity, rtprio_thread } alongside the chain's sc() thunk.

saveThreadAttrs: read the CALLING thread's current cpuset affinity mask and
realtime priority. `sc` is the chain's syscall thunk; `sys` the syscall
numbers; `maskAddr`/`prioAddr` are the native addresses of a 0x10-byte mask
buffer and a 4-byte rtprio struct. Returns { mask: int64,
prio: [type, prio] } or null if either lookup failed.
*/
export function saveThreadAttrs(sc, sys, maskAddr, prioAddr, maskDv, prioDv) {
    const ID = THREAD_ID_ALL();
    const aff = sc(sys.cpuset_getaffinity, CPU_LEVEL_WHICH,
        CPU_WHICH_TID, ID, THREAD_ATTR_MASK_SIZE, maskAddr).i32;
    const prio = sc(sys.rtprio_thread, RTP_LOOKUP, 0, prioAddr).i32;
    if (aff !== 0 || prio !== 0) return null;
    return {
        mask: new int64(maskDv.getUint32(0, true), maskDv.getUint32(4, true)),
        prio: [prioDv.getUint16(0, true), prioDv.getUint16(2, true)],
    };
}

/*
restoreMainThread: put the calling thread back on its saved mask/prio,
widening affinity BEFORE dropping priority (the reverse order can leave a
realtime thread stranded on a core it is no longer allowed to run on), then
read both back. Returns { affinitySet, rtprioSet, mask, prio, ok } -- ok is
true only if both readbacks match what was saved.
*/
export function restoreMainThread(sc, sys, saved, maskAddr, prioAddr, maskDv, prioDv) {
    const ID = THREAD_ID_ALL();
    maskDv.setUint32(0, saved.mask.low, true);
    maskDv.setUint32(4, saved.mask.hi, true);
    const affinitySet = sc(sys.cpuset_setaffinity, CPU_LEVEL_WHICH,
        CPU_WHICH_TID, ID, THREAD_ATTR_MASK_SIZE, maskAddr).i32;
    prioDv.setUint16(0, saved.prio[0], true);
    prioDv.setUint16(2, saved.prio[1], true);
    const rtprioSet = sc(sys.rtprio_thread, RTP_SET, 0, prioAddr).i32;

    maskDv.setUint32(0, 0, true);
    maskDv.setUint32(4, 0, true);
    sc(sys.cpuset_getaffinity, CPU_LEVEL_WHICH, CPU_WHICH_TID, ID,
        THREAD_ATTR_MASK_SIZE, maskAddr);
    const backMask = new int64(maskDv.getUint32(0, true), maskDv.getUint32(4, true));
    prioDv.setUint16(0, 0xffff, true);
    prioDv.setUint16(2, 0xffff, true);
    sc(sys.rtprio_thread, RTP_LOOKUP, 0, prioAddr);
    const backPrio = [prioDv.getUint16(0, true), prioDv.getUint16(2, true)];
    const ok = backMask.low === saved.mask.low && backMask.hi === saved.mask.hi
        && backPrio[0] === saved.prio[0] && backPrio[1] === saved.prio[1];
    return {
        affinitySet, rtprioSet,
        mask: backMask, prio: backPrio,
        ok,
    };
}

/*
pinMainThread: set affinity to `core` and realtime priority `rtp`.
Returns { affinitySet, rtprioSet } -- zero on success, -1/errno otherwise.
*/
export function pinMainThread(sc, sys, core, rtp, maskAddr, prioAddr, maskDv, prioDv) {
    const ID = THREAD_ID_ALL();
    maskDv.setUint32(0, 1 << core, true);
    prioDv.setUint16(0, rtp, true);   // rtprio.type = RTP_PRIO_REALTIME
    prioDv.setUint16(2, 0, true);     // rtprio.prio filled in by the caller
    const affinitySet = sc(sys.cpuset_setaffinity, CPU_LEVEL_WHICH,
        CPU_WHICH_TID, ID, THREAD_ATTR_MASK_SIZE, maskAddr).i32;
    const rtprioSet = sc(sys.rtprio_thread, RTP_SET, 0, prioAddr).i32;
    return { affinitySet, rtprioSet };
}
