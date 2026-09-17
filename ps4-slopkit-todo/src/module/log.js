// Shared logging/status layer for the exploit chains (lapse.js, netctrl.js).
// Both chains used to carry private copies of run/post/terse/mark/state/check/hx;
// they differ only in report prefix, highlight regexes and whether post() sends
// the terse or raw detail, so those are init options here.

const VERBOSE = new URLSearchParams(location.search).get("verbose") === "1";

const PROSE = [
    / -- /, /\.\s/, /;\s/,
    /,\s+(which|so|and that|because|since|as that)\s/,
    /,\s+\w+\s+of\s+which\s/,
    /\s+(because|rather than|instead of|so that|which is|which means|which the|so the|with the aim)\s/,
    /\s+so\s+[a-z]/,
    /\s+\([a-z][^)]{40,}\)/,
];

let outEl = null, stateEl = null;
let onLog = console.log, onStatus = () => {};
let postPrefix = "PS4", postRawDetail = false;
let badRe = null, warnRe = null, okRe = null;
let passCount = 0, failCount = 0;

export function initLog(options) {
    onLog = options.onLog || console.log;
    onStatus = options.onStatus || (() => {});
    postPrefix = options.postPrefix || "PS4";
    postRawDetail = !!options.postRawDetail;
    badRe = options.badRe || /FAIL|ERROR|THREW|MISMATCH|WRONG|MISSING|TIMEOUT|NOT-FOUND/i;
    warnRe = options.warnRe || /SKIP|GAP|WOULD-HAVE-WON|WARN/i;
    okRe = options.okRe || /OK|PROVEN|READY|pass|BASELINE/i;

    // The chains expect these as globals (payload-era code paths reference them).
    globalThis.mark = function(tag, detail) { onLog(tag, detail); };
    globalThis.state = function(msg, cls) { onStatus(msg, cls); };
    outEl = document.getElementById('console');
    stateEl = document.getElementById('statusText');
    /*
    append-mode log: start from an empty element so the O(1) append below
    never stacks under whatever the page shipped inside #console. Doing it
    once here is the only innerHTML write left in this file.
    */
    if (outEl) outEl.innerHTML = "";
    lines.length = 0;
    // Also publish them globally so bare-global references in the chains work.
    globalThis.outEl = outEl;
    globalThis.stateEl = stateEl;

    /*
    ONE WRITER FOR #console.

    includes/script.js's window.logToUI does `consoleEl.textContent += ...`,
    which DESTROYS every child <div> appendLine() built and flattens the tail
    of the log into one run (the \n never renders; #console has no
    white-space: pre). main.js calls logToUI for its FW/UI/LOAD/MAIN lines, so
    the first [MAIN] line after a run wiped the whole <div> tree mark() had
    built -- the "mess" at the end of the box.

    Re-route logToUI through the SAME append path so the two writers can no
    longer clobber each other, keeping script.js's timestamped [TAG] shape.
    Published as globalThis.logLine too (a stable bare-global for the chains).
    */
    globalThis.logLine = appendLine;
    globalThis.logToUI = function (tag, message) {
        if (!outEl) return;
        const ts = new Date().toLocaleTimeString();
        const prefix = tag ? `[${tag}] ` : '';
        appendLine(`[${ts}] ${prefix}${message == null ? '' : message}`);
        outEl.scrollTop = outEl.scrollHeight;
    };
}

export function checkCounts() { return { passCount, failCount }; }

/*
ORDERED POSTS.

This used to open a fresh XMLHttpRequest per call and fire them all
asynchronously. At teardown the chains emit ~15 marks in a tight loop
(FDS-CLOSED, THREAD-ATTRS-RESTORED, WORKER-DISARMED, WORKER-UNWIRED,
EXPM1-RESTORED, PROOF-SUMMARY-FINAL, SAFE-TO-EXIT, ...), so 15 requests
raced to the same endpoint and the receiver concatenated them in
COMPLETION order. netctrl makes this worse by posting the RAW detail
(postRawDetail), so each body is long and the interleaving is visible:
two lines spliced together mid-word, and fragments like "11:0" that were
really "113:0".

One request in flight at a time, drained in FIFO order, removes the race
entirely. Nothing else changes -- same URL, same method, same body shape.
The queue is drained synchronously on send() so a mark() never blocks the
exploit path; the actual network work happens on the XHR's own callbacks.
*/
const postQueue = [];
let postInFlight = false;

function drainPostQueue() {
    if (postInFlight || !postQueue.length) return;
    const body = postQueue.shift();
    postInFlight = true;
    let x = null;
    try {
        x = new XMLHttpRequest();
        x.open("POST", "t", true);
        x.setRequestHeader("Content-Type", "application/x-www-form-urlencoded");
        x.onreadystatechange = function () {
            if (x.readyState === 4) { postInFlight = false; drainPostQueue(); }
        };
        x.onerror = function () { postInFlight = false; drainPostQueue(); };
        x.send(body);
    } catch (e) {
        postInFlight = false;
        drainPostQueue();
    }
}

export function post(tag, detail) {
    try {
        const x = new XMLHttpRequest();
        x.open("POST", "t", true);
        x.setRequestHeader("Content-Type", "application/x-www-form-urlencoded");
        x.send(postPrefix + "&tag=" + encodeURIComponent(tag)
             + "&detail=" + encodeURIComponent(String(detail == null ? "" : detail)));
    } catch (e) { }
}

function terse(s) {
    if (VERBOSE || s == null) return s;
    s = String(s);
    for (const re of PROSE) {
        const m = re.exec(s);
        if (m && m.index > 0) s = s.slice(0, m.index);
    }
    s = s.replace(/\s+$/, "");
    if (s.length > 140) s = s.slice(0, 140) + "...";
    return s;
}

const lines = [];

/*
PERFORMANCE / WATCHDOG FIX.

This is the real cause of the "page isn't responding" popups during the
late stages, not the kernel loops.

mark() used to rebuild the WHOLE log on every call:

    lines.push(...);
    outEl.innerHTML = lines.map(esc + wrap).join("\n");
    outEl.scrollTop = outEl.scrollHeight;

A run this long produces 1000+ marks. By the time netctrl/lapse reach
KernelView, every single mark re-parsed and re-laid-out the entire
accumulated log as fresh HTML, and the scrollTop write forced a
synchronous layout flush on top of it. The browser blocks on that
rebuild -- and because the exploit yields between heavy ops (breathe()),
the watchdog sees a long synchronous DOM stretch and pops the dialog.

Append instead. One <div> per line, inserted below the existing ones,
and only a cheap scrollTop write. DOM work per mark is now O(1) instead
of O(total lines). The colour span wrapping is preserved verbatim so
the log looks identical.
*/
/*
APPEND, ALWAYS APPEND -- never assign textContent/innerHTML on outEl.

Both the exploit chains (via mark()) AND includes/script.js (via
window.logToUI, called by main.js for its own FW/UI/MAIN lines) write to
the same #console element. logToUI used to do:

    consoleEl.textContent += `[${ts}] ${prefix}${message}\n`;

Setting textContent on a node DESTROYS every child element and replaces
them with one flat text node. So the first [MAIN] line after a run
wiped the entire <div> tree mark() had built and collapsed the tail of
the log into an unbroken run -- which is the "mess" at the end of the
box. (The \n never rendered either: #console is a plain block with no
white-space: pre.)

appendLine is therefore published as globalThis.logLine so logToUI calls
the SAME path and the two writers can no longer clobber each other.
*/
function appendLine(l) {
    const c = badRe.test(l) ? "bad" : warnRe.test(l) ? "warn" : okRe.test(l) ? "ok" : "";
    const div = document.createElement("div");
    if (c) div.className = c;
    div.textContent = l;
    outEl.appendChild(div);
}


/*
CRASH-SURVIVING TRAIL.

Every mark() so far has gone to exactly two places: the #console DOM and an
XHR. Both live INSIDE the WebProcess. When the WebProcess dies -- the
"not enough free system memory" page -- the DOM dies with it and the XHR in
flight is never read, so the last line before the crash is simply gone. That
is why the popup is unscreenshotable: the evidence disappears at the same
instant as the process.

The kernel fault we are chasing happens on the main thread inside a
synchronous sc() call, so there is no JS try/catch that can run afterwards --
nothing on the JS side gets a chance to report. The only thing that survives
the process is storage the BROWSER PROCESS owns: localStorage.

So mirror every mark() into localStorage, and console.log it as well so the
Web Inspector console (which is attached to the browser process, not the
dead WebProcess) also has the tail.

Reading it back after a crash: open the console on the page and run
  JSON.parse(localStorage.getItem('ps4lab_trail'))
The LAST entry is the last step that COMPLETED. The step that killed the
process is the NEXT one in the source. Bump ?trail=0 to disable if this is
somehow suspected of affecting timing.
*/
const TRAIL_ON = new URLSearchParams(location.search).get("trail") !== "0";
const TRAIL_KEY = "ps4lab_trail";
const TRAIL_MAX = 400;
let trail = [];

/*
WATCHDOG FIX.

trailPush used to do a full JSON.stringify(trail) + localStorage.setItem on
EVERY mark(). localStorage.setItem is SYNCHRONOUS and blocking, and by the
late stages a run has emitted 1000+ marks, so this became a stringify of up
to 400 entries plus a storage write on every single line -- with no yield.
That is a large part of the unbroken synchronous stretch that trips the
browser watchdog right after KV-RW64 (the last line in the "page isn't
responding" screenshot).

The crash-surviving purpose only needs the trail to be IN storage, not
re-written on every line: after a WebProcess death the LAST persisted entry
is still the last completed step, which is what the read-back procedure
(JSON.parse(localStorage.getItem('ps4lab_trail'))) documents. So keep every
entry in the in-memory `trail` (never lost while the process lives), but
only serialise to storage on a time budget -- and always on an entry that
looks like a terminal/interesting one, plus on the way out via trailFlush().
*/
const TRAIL_SAVE_MS = 250;
let trailLastSave = 0;

function trailSave() {
    try { localStorage.setItem(TRAIL_KEY, JSON.stringify(trail)); } catch (e) { }
    trailLastSave = Date.now();
}

export function trailFlush() { if (TRAIL_ON) trailSave(); }

function trailPush(tag, detail) {
    if (!TRAIL_ON) return;
    const at = Date.now();
    const parts = [String(at), String(tag)];
    if (detail != null && String(detail) !== '') parts.push(String(detail));
    const entry = parts.join('  ');
    trail.push(entry);
    if (trail.length > TRAIL_MAX) trail.splice(0, trail.length - TRAIL_MAX);
    /*
    console.log FIRST, before the storage write: it is synchronous to the
    browser-process console and cannot fail, whereas localStorage.setItem can
    throw (quota) or be slow. Order matters here -- we want the Inspector tail
    even if storage gives up.
    */
    try { console.log("[TRAIL] " + tag + (detail ? "  " + detail : "")); }
    catch (e) { }
    /* Time-throttled rather than per-mark: see the note above. */
    if (Date.now() - trailLastSave >= TRAIL_SAVE_MS) trailSave();
}

/* Called by the chains at the top of a run so a previous crash's tail is not
   mistaken for this run's. */
export function trailReset() {
    trail = [];
    trailLastSave = 0;
    try { localStorage.removeItem(TRAIL_KEY); } catch (e) { }
}

/* Terminal tags whose detail must be persisted immediately, throttled or not:
   after a WebProcess death these are the entries worth having in storage. */
const TRAIL_CRITICAL = /PROOF-(FAIL|SUMMARY)|SAFE-TO-EXIT|REBOOT|PANIC|FATAL|DEAD|REFUSING/i;

export function mark(tag, detail) {
    const raw = detail;
    detail = terse(detail);
    const line = tag + (detail == null || detail === "" ? "" : "  " + detail);
    trailPush(tag, detail);
    if (TRAIL_ON && TRAIL_CRITICAL.test(tag)) trailSave();
    lines.push(line);
    appendLine(line);
    outEl.scrollTop = outEl.scrollHeight;
    post(tag, postRawDetail ? raw : detail);
}

export function trace(tag, detail) { if (VERBOSE) mark(tag, detail); else post(tag, detail); }

export function state(t, c) { stateEl.textContent = t; stateEl.className = c || ""; }

/*
================================================================================
PRIMITIVE PROGRESS REPORTER (userland stage UX)
================================================================================

The SSV primitive retries grooms until it lands -- routinely 5-8 attempts. Both
chains used to leave the user staring at a static "running the primitive..."
status with only the occasional AUTO-RETRY-AFTER-FAILURE line, which reads like
a terminal failure loop even though it is working. The two chains then diverged
badly: netctrl suppressed almost everything (only FAIL/RETRY reached the UI),
lapse printed every event (a flood).

This builds one reporter both can use with the SAME shape:

  * the STATUS line becomes a live "attempt N/M - <phase>" that changes as the
    groom advances, so the page never looks frozen;
  * a bounded set of MILESTONE marks reaches the log -- one per phase the first
    time it is seen, plus one line per retry with the attempt budget -- so the
    log stays short and every line means something;
  * everything else is still sent verbatim to the XHR via trace(), so no
    evidence is lost from the server-side transcript.

Usage:
  const progress = makePrimitiveProgress(6);
  onEvent: progress.onEvent
  ...after establishPrimitive resolves: progress.done("ok"|"error")

`maxAttempts` mirrors what is passed to establishPrimitive so the "N/M" is the
real budget, not a guess.
*/
export function makePrimitiveProgress(maxAttempts) {
    const seenPhase = new Set();
    let lastAttempt = -1;
    let phases = 0;
    const budget = maxAttempts > 0 ? "" + maxAttempts : "?";

    return {
        onEvent: function (t, d, a) {
            const att = (a != null && a > 0) ? a : lastAttempt;
            const isRetry = /RETRY/i.test(t);

            /* Live status: attempt + phase name. Updated on EVERY event, so a
               slow groom still shows the page as working. */
            state("primitive: attempt " + (att > 0 ? att : "?") + "/" + budget
                + " - " + t.toLowerCase() + "...", "warn");

            if (isRetry) {
                lastAttempt = att;
                mark("PRIMITIVE-RETRY", "attempt " + att + "/" + budget
                    + "" + (d ? "  " + d : ""));
                return;
            }

            /*
            MISS / GIVE-UP DETAIL IS ALWAYS LOGGED, never only on first sighting.

            Every attempt that misses emits the SAME tag (SSV-PLACEMENT-MISS,
            ZERO-HEADER-MISS, GIVE-UP...). The seenPhase dedupe below therefore
            printed the first one and routed attempts 2..N to trace() -- XHR only,
            invisible in the page log. A run that missed six times with three
            different reasons showed exactly one of them, which is how "gave up
            after 6 attempts" arrived with no explanation attached.

            These tags are terminal for their attempt, so each one is worth a
            line: a handful per run, not a flood.
            */
            const isMissOrEnd = /MISS|GIVE-UP|GIVEUP|THREW|CEILING|CANCEL/i.test(t);
            if (isMissOrEnd) {
                seenPhase.add(t);
                mark("PRIMITIVE-MISS", "[" + (att > 0 ? att : "?") + "] " + t
                    + (d ? "  " + d : ""));
                return;
            }

            /* Milestone: first sighting of a distinct phase, capped so a long
               groom cannot pile up lines. */
            if (!seenPhase.has(t) && phases < 40) {
                seenPhase.add(t);
                phases++;
                mark("PRIMITIVE-PHASE", "[" + (att > 0 ? att : "?") + "] " + t
                    + (d ? "  " + d : ""));
                return;
            }

            /* Everything else: server-side transcript only. */
            trace(t, (a != null ? "[" + a + "] " : "") + (d || ""));
        },
        done: function (cls) {
            state(cls === "ok" ? "primitive established"
                : "primitive failed", cls === "ok" ? "ok" : "error");
        }
    };
}

export function check(name, ok, detail) {
    if (ok) { passCount++; mark("PROOF-OK", name + (detail ? "  " + detail : "")); }
    else { failCount++; mark("PROOF-FAIL", name + (detail ? "  " + detail : "")); }
    return ok;
}

export function hx(n) { return "0x" + (n >>> 0).toString(16); }

/*
Byte formatting. lapse.js and netctrl.js each carried byte-for-byte
identical private copies of these, used for hex dumps of gadget bytes,
kpatch headers, ELF heads and pthread-byte probes. They sit here beside hx
because they are the same concern: rendering bytes for a log line.
*/
export function hexByte(b) { return (b < 16 ? "0" : "") + (b & 0xff).toString(16); }

export function hexBytes(a) {
    let s = "";
    for (let i = 0; i < a.length; ++i) s += (i ? " " : "") + hexByte(a[i]);
    return s;
}

// Common entry-point wrapper: both chains' run() were byte-identical apart from
// which runOriginal they invoked.
export async function runChain(options, runOriginal) {
    initLog(options);
    const result = await runOriginal();
    return result || { success: false, reason: "exploit did not establish success" };
}
