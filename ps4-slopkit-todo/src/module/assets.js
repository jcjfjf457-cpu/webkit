export function kpatchPath(firmwareKey, offsets) {
    if (offsets && offsets.kpatch)
        return "src/kpatch/" + offsets.kpatch;
    return firmwareKey ? "src/kpatch/" + firmwareKey.replace(".", "") + ".bin" : null;
}

/*
Scan a kpatch blob for its conditional-jump gate sites: the pattern is
`c6 81 <rel32>` followed by `eb` six bytes later. Returns the rel32 targets
as unsigned offsets from the kernel base. Used by both lapse.js and netctrl.js.
*/
export function kpatchJmpSites(kpatch) {
    const sites = [];
    if (!kpatch) return sites;
    for (let i = 0; i + 7 <= kpatch.length; ++i) {
        if (kpatch[i] !== 0xc6 || kpatch[i + 1] !== 0x81) continue;
        if (kpatch[i + 6] !== 0xeb) continue;
        sites.push(((kpatch[i + 2]) | (kpatch[i + 3] << 8)
            | (kpatch[i + 4] << 16) | (kpatch[i + 5] << 24)) >>> 0);
    }
    return sites;
}

export async function loadBinary(path) {
    if (!path) return null;
    const response = await fetch(path);
    if (!response.ok) return null;
    return new Uint8Array(await response.arrayBuffer());
}

/*
payload.bin lives beside main.js, lapse.js, and netctrl.js in src/.
Resolve it from this module so both exploit chains use the same URL:
src/module/assets.js -> ../payload.bin == src/payload.bin.
*/
export async function loadPayload() {
    const url = new URL("../payload.bin", import.meta.url);
    const response = await fetch(url.href, { cache: "no-store" });
    if (!response.ok)
        throw new Error("payload fetch failed: HTTP " + response.status
            + " at " + url.href);
    const bytes = new Uint8Array(await response.arrayBuffer());
    if (bytes.length === 0)
        throw new Error("payload fetch returned an empty file: " + url.href);
    return bytes;
}
