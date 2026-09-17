/*
Shared address predicates for the exploit chains (lapse.js, netctrl.js).

Both chains grew their own copies of these three tests, and netctrl ended up
with FOUR spellings of the same "is this a kernel pointer" question
(kptr, kptr2, isKptr, and an inline hi>=0xffff0000 check). They are not
interchangeable by accident -- they encode three DIFFERENT questions -- so
they live here under names that say which one they answer.

Why three tests and not one:

  isKernelPtr()  "does this look like kernel virtual memory at all?"
                 A 64-bit kernel address has the top 16 bits set (the PS4
                 kernel is mapped in the high half; canonical kernel space
                 starts at 0xffff800000, and everything we see is
                 >= 0xffff0000 high). Used to reject a zero-filled or
                 reclaimed read before dereferencing it.

  isPtrish()     "is this a JS-heap pointer to a tagged JSValue cell?"
                 The JSC heap on this target lives well under 0x10000 in the
                 high word, and cell pointers are 8-byte aligned. Used only
                 during the worker-memory walk.

  isImageAddr()  "is this inside the kernel IMAGE, specifically?"
                 &allproc and sysent sy_call sit in the kernel's text/data, and
                 both exploits spell that test as high == 0xffff -- lapse's
                 inImageAddr (used on the allproc walk and the sysent sy_call
                 gate) and netctrl's kl_lock check. Stricter than
                 isKernelPtr: a heap/slab pointer is a kernel pointer but NOT
                 an image address, and widening this one would silently let
                 the allproc walk and the sysent gate accept non-image
                 pointers.

Keeping them distinct is the point. NOTE the two spellings are load-
bearing and must not be unified: isKernelPtr is >= 0xffff0000 (all four of
netctrl's kptr/kptr2/isKptr/kAligned spellings, and lapse's inner kptr),
while isImageAddr is == 0xffff. An earlier draft of this file wrote
isImageAddr as == 0xffff and would have broken both call sites.
*/

// Kernel virtual memory: high 16 bits set.
export function isKernelPtr(v) {
    return !!v && (v.hi >>> 0) >= 0xffff0000;
}

/*
8-byte aligned kernel pointer. Used before spending a kernel R/W op on an
address -- an unaligned pointer through a UIO_SYSSPACE uio is a bad deref.
*/
export function isKernelPtrAligned(v) {
    return isKernelPtr(v) && ((v.low >>> 0) & 7) === 0;
}

// JS-heap tagged cell pointer (worker/object walk).
export function isPtrish(v) {
    return !!v && v.hi > 0 && v.hi < 0x10000 && (v.low & 7) === 0;
}

/*
Inside the kernel image: high word is all ones (0xffff). Matches
lapse's inImageAddr and netctrl's kl_lock gate. See the header note
before changing this to the isKernelPtr bound.
*/
export function isImageAddr(v) {
    return !!v && (v.hi >>> 0) === 0xffffffff;
}

/*
Module base plausibility: a 0x4000-aligned address above zero. lapse used
this on the webkit/libkernel bases, netctrl inlined the same test inline.
*/
export function isPlausibleBase(v) {
    return !!v && v.hi > 0 && (v.low & 0x3fff) === 0;
}

// Two int64s equal by unsigned 32-bit halves.
export function sameI64(a, b) {
    return !!a && !!b
        && (a.low >>> 0) === (b.low >>> 0)
        && (a.hi >>> 0) === (b.hi >>> 0);
}
