// DOM References
const consoleEl = document.getElementById('console');
const fwDisplay = document.getElementById('fwDisplay');
const jeilbrekBtn = document.getElementById('jeilbrek');
const checkbox = document.getElementById('autoJbInput');
const label = document.getElementById('autoJbLabel');
const kexForm = document.getElementById('kernel-options');
const netctrlRadio = document.getElementById('netctrl-exploit');
const lapseRadio = document.getElementById('lapse-exploit');
const statusText = document.getElementById('statusText');
const statusDot = document.getElementById('statusDot');

// State
let timerId = null;
let exploitChain = localStorage.getItem('exploitChain') || 'lapse';
const storedAutoJb = localStorage.getItem('autoJb');
let autoJbValue = storedAutoJb !== null ? storedAutoJb === 'true' : false;

// Logger
window.logToUI = function(tag, message) {
    if (!consoleEl) return;
    const ts = new Date().toLocaleTimeString();
    const prefix = tag ? `[${tag}] ` : '';
    const line = document.createElement('div');
    line.textContent = `[${ts}] ${prefix}${message || ''}`;
    consoleEl.appendChild(line);
    consoleEl.scrollTop = consoleEl.scrollHeight;
};

let jailbreakStarted = false;

// Status
window.setStatus = function(msg, cls = '') {
    if (statusText) statusText.textContent = msg;
    if (statusDot) {
        statusDot.className = 'status-dot';
        if (cls) statusDot.classList.add(cls);
    }

    if (cls === 'running') {
        jailbreakStarted = true;
    }
    if (jailbreakStarted) {
        const m = String(msg || '');
        if (/^already jailbroken/i.test(m)) document.title = '\u2713 Already jailbroken';
        else if (/^done$/i.test(m)) document.title = '\u2713 Jailbroken';
        else if (/^partial success/i.test(m)) document.title = 'Jailbreak partial';
        else if (cls === 'ok') document.title = '\u2713 Jailbroken';
        else if (cls === 'warn') document.title = 'Jailbreak partial';
        else if (cls === 'error') document.title = 'Jailbreak failed';
        else if (cls === 'running') document.title = 'Jailbreaking...';
    }
};

// Getters
window.getExploitChain = function() { return exploitChain; };
window.getAutoJbValue = function() { return autoJbValue; };

//  Internal functions
function stopInterval() {
    if (timerId) { clearInterval(timerId); timerId = null; }
    if (label) label.textContent = 'Auto Jailbreak';
}

function jailbreakCountdown() {
    stopInterval();
    let countdown = 5;
    if (label) label.textContent = `Auto Jailbreaking in: ${countdown}`;
    timerId = setInterval(() => {
        countdown--;
        if (label) label.textContent = `Auto Jailbreaking in: ${countdown}`;
        if (countdown < 0) {
            clearInterval(timerId); timerId = null;
            if (label) label.textContent = 'Executing';
            window.setStatus('Auto executing...', 'running');
            if (jeilbrekBtn) jeilbrekBtn.disabled = true;
            if (typeof window.doJb === 'function') {
                window.doJb();
            } else {
                window.logToUI('ERROR', 'doJb not defined');
            }
        }
    }, 1000);
}

// Cache handling
let lastCachePercent = -1;

function cacheProgress(e) {
    if (jailbreakStarted) return;
    if (e.total > 0) {
        const Percent = Math.round((e.loaded / e.total) * 100);
        document.title = 'Caching: ' + Percent + '%';
        if (Percent !== lastCachePercent) {
            lastCachePercent = Percent;
        }
    } else {
        document.title = 'Caching...';
    }
}

function cacheDone() {
    displayCacheProgress();
}

function displayCacheProgress() {
    setTimeout(function() {
        if (jailbreakStarted) return;
        document.title = '\u2713 Cached';
    }, 1000);
    setTimeout(function() {
        if (jailbreakStarted) return;
        document.title = 'PS4 SlopKit Exploit';
    }, 3000);
}

// Setup UI (called by main.js)
window.setupUI = function() {
    // Firmware detection (global offsetsFor from main.js)
    let forceNetctrl = false;
    let firmwareSupported = false;
    if (fwDisplay && typeof window.offsetsFor === 'function') {
        const { key, off } = window.offsetsFor(navigator.userAgent);
        const onPs4 = key !== null;
        fwDisplay.textContent = key || (onPs4 ? 'UNSUPPORTED' : 'NOT PS4');
        const firmwareVersion = key ? Number(key) : NaN;
        const unsupportedFirmware = !off;
        firmwareSupported = !unsupportedFirmware;
        forceNetctrl = !unsupportedFirmware
            && Number.isFinite(firmwareVersion) && firmwareVersion >= 12.50;
        if (unsupportedFirmware) {
            [netctrlRadio, lapseRadio].forEach(function(radio) {
                if (radio) {
                    radio.disabled = true;
                    if (radio.parentNode) {
                        radio.parentNode.classList.add('firmware-unsupported');
                    }
                }
            });
        }
        if (forceNetctrl) {
            exploitChain = 'netctrl';
            localStorage.setItem('exploitChain', exploitChain);
            if (netctrlRadio) netctrlRadio.checked = true;
            if (lapseRadio) {
                lapseRadio.checked = false;
                lapseRadio.disabled = true;
                if (lapseRadio.parentNode) {
                    lapseRadio.parentNode.classList.add('lapse-disabled');
                }
            }
        }
        if (!off) {
            jeilbrekBtn.disabled = true;
            if (!onPs4) {
                window.logToUI('FW', 'The user required to be on PS4');
            } else {
                window.logToUI('FW', 'Unsupported firmware.');
            }
            window.setStatus('Unsupported', 'error');
        } else {
            window.logToUI('FW', 'Detected ' + key);
            window.setStatus('Ready', 'ok');
        }
    } else {
        [netctrlRadio, lapseRadio].forEach(function(radio) {
            if (radio) {
                radio.disabled = true;
                if (radio.parentNode) {
                    radio.parentNode.classList.add('firmware-unsupported');
                }
            }
        });
        if (jeilbrekBtn) jeilbrekBtn.disabled = true;
        window.logToUI('FW', 'offsetsFor not available');
        window.setStatus('Unsupported', 'error');
    }

    // Exploit selection
    if (kexForm) {
        kexForm.addEventListener('change', function(e) {
            if (e.target.name === 'kernel') {
                if (forceNetctrl && e.target.value === 'lapse') {
                    if (netctrlRadio) netctrlRadio.checked = true;
                    return;
                }
                localStorage.setItem('exploitChain', e.target.value);
                exploitChain = e.target.value;
                window.logToUI('UI', 'Exploit switched to: ' + exploitChain);
            }
        });

        kexForm.addEventListener('click', function(e) {
            if (!forceNetctrl) return;
            if (!e.target.closest || !e.target.closest('.radio-option')) return;
            if (!lapseRadio) return;
            if (!e.target.closest('.radio-option').contains(lapseRadio)) return;

            // Keep Netcontrol selected and tell the user why Lapse is not available on this firmware.
            if (netctrlRadio) netctrlRadio.checked = true;
            exploitChain = 'netctrl';
            window.logToUI('FW', 'Firmware 12.50+ requires Netcontrol.');
        });
    }
    if (forceNetctrl) exploitChain = 'netctrl';
    if (exploitChain === 'netctrl' && netctrlRadio) netctrlRadio.checked = true;
    else if (lapseRadio) lapseRadio.checked = true;

    // Auto-jailbreak checkbox
    if (checkbox) {
        checkbox.checked = autoJbValue;
        checkbox.addEventListener('change', function() {
            localStorage.setItem('autoJb', checkbox.checked);
            autoJbValue = checkbox.checked;
            if (checkbox.checked && !jeilbrekBtn.disabled) {
                jailbreakCountdown();
            } else {
                stopInterval();
            }
        });
    }

    // Jailbreak button
    if (jeilbrekBtn) {
        jeilbrekBtn.addEventListener('click', function() {
            jeilbrekBtn.disabled = true;
            stopInterval();
            window.setStatus('Manual start...', 'running');
            if (typeof window.doJb === 'function') {
                window.doJb();
            } else {
                window.logToUI('ERROR', 'doJb not defined');
            }
        });
    }

    // Cache events
    if (window.applicationCache) {
        const ac = window.applicationCache;
        ac.addEventListener('progress', cacheProgress, false);
        ac.addEventListener('cached', cacheDone, false);
        ac.addEventListener('updateready', function() {
            try { ac.swapCache(); } catch (_) {}
            cacheDone();
        }, false);
        ac.addEventListener('noupdate', function() {
            if (jailbreakStarted) return;
            document.title = 'PS4 SlopKit Exploit';
        }, false);
    }

    // Auto-start
    if (autoJbValue && jeilbrekBtn && !jeilbrekBtn.disabled) {
        jailbreakCountdown();
    }

    if (firmwareSupported) {
        window.logToUI('UI', 'Ready.');
        window.setStatus('Idle', '');
    }
};
