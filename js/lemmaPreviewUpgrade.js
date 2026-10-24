/**
 * Two-phase lean page upgrade (JS-owned).
 *
 * PHP paints the CodeCogs / #lemma-shell shell first (plain ?module=…, no
 * &preview=1 in the address bar), then boots this file after first paint.
 * We load the same Vue/KaTeX/CodeMirror stack as the full lemma.php branch and
 * swap the shell for createApp('render', code).
 *
 * ---------------------------------------------------------------------------
 * Contract for PHP (shell-first response)
 * ---------------------------------------------------------------------------
 * 1. Emit #lemma-stage > #lemma-shell (existing preview shell HTML + CSS).
 * 2. Embed lemma payload once, either:
 *      window.__LEMMA_CODE__ = <json>;
 *    or:
 *      <script type="application/json" id="lemma-code">…</script>
 * 3. Prefer also emitting the CodeMirror importmap (lemma_emit_codemirror_importmap)
 *    before this script. Otherwise set window.__LEMMA_IMPORTMAP__ = {imports:{…}}.
 * 4. After shell HTML, load this file without blocking first paint, e.g.:
 *      <script src="js/lemmaPreviewUpgrade.js?v=9" defer></script>
 *    or a one-liner after paint:
 *      requestAnimationFrame(function () { lemmaPreviewUpgrade(); });
 * 5. Do NOT put &preview=1 in public URLs; two-phase is internal under ?module=.
 *
 * Optional globals:
 *   window.__LEMMA_ASSET_V__              cache-bust for py.js/std.js (default "9")
 *   window.__LEMMA_PREVIEW_UPGRADE_AUTO__ set false to only expose the API
 *   window.__LEMMA_IMPORTMAP__            { imports: {…} } if importmap not in DOM
 *
 * Public API:
 *   window.lemmaPreviewUpgrade(opts?) → Promise<app|undefined>
 *   opts: { code, importMap, assetV, replaceSelector, mountId }
 */
(function (global) {
	"use strict";

	var DEFAULT_ASSET_V = "9";
	var CLASSIC_SCRIPTS = [
		"node_modules/axios/dist/axios.min.js",
		"node_modules/qs/dist/qs.js",
		"node_modules/vue/dist/vue.global.prod.js",
		"node_modules/vue3-sfc-loader/dist/vue3-sfc-loader.js",
	];
	var DEFERRED_CLASSIC = [
		"node_modules/clipboard/dist/clipboard.min.js",
		"node_modules/file-saver/dist/FileSaver.min.js",
		"node_modules/lz-string/libs/lz-string.js",
		"node_modules/katex/dist/katex.min.js",
		"node_modules/katex/dist/contrib/auto-render.min.js",
		"node_modules/prismjs/prism.js",
		"js/prism-lean.js",
	];
	var STYLES = [
		"css/codemirror-overrides.css",
		"node_modules/katex/dist/katex.min.css",
		"node_modules/prismjs/themes/prism.min.css",
	];

	function assetV(opts) {
		if (opts && opts.assetV != null) return String(opts.assetV);
		if (global.__LEMMA_ASSET_V__ != null) return String(global.__LEMMA_ASSET_V__);
		return DEFAULT_ASSET_V;
	}

	function absUrl(src) {
		try {
			return new URL(src, document.baseURI || location.href).href;
		} catch (e) {
			return src;
		}
	}

	function bareSrc(src) {
		return absUrl(String(src).replace(/[?&]v=[^&]*/g, "").replace(/\?$/, "").replace(/&$/, ""));
	}

	function alreadyHaveScript(src) {
		var want = bareSrc(src);
		var nodes = document.querySelectorAll("script[src]");
		for (var i = 0; i < nodes.length; i++) {
			if (bareSrc(nodes[i].getAttribute("src") || "") === want) return true;
		}
		return false;
	}

	function alreadyHaveCss(href) {
		var want = absUrl(href);
		var nodes = document.querySelectorAll('link[rel="stylesheet"][href]');
		for (var i = 0; i < nodes.length; i++) {
			if (absUrl(nodes[i].getAttribute("href") || "") === want) return true;
		}
		return false;
	}

	function loadCss(href) {
		if (alreadyHaveCss(href)) return Promise.resolve();
		return new Promise(function (resolve, reject) {
			var link = document.createElement("link");
			link.rel = "stylesheet";
			link.href = href;
			link.onload = function () { resolve(); };
			link.onerror = function () { reject(new Error("css failed: " + href)); };
			document.head.appendChild(link);
		});
	}

	function loadClassicScript(src) {
		if (alreadyHaveScript(src)) return Promise.resolve();
		return new Promise(function (resolve, reject) {
			var s = document.createElement("script");
			s.src = src;
			s.async = false;
			s.onload = function () { resolve(); };
			s.onerror = function () { reject(new Error("script failed: " + src)); };
			(document.body || document.head).appendChild(s);
		});
	}

	function loadModuleScript(src) {
		if (alreadyHaveScript(src)) return Promise.resolve();
		return new Promise(function (resolve, reject) {
			var s = document.createElement("script");
			s.type = "module";
			s.src = src;
			s.onload = function () { resolve(); };
			s.onerror = function () { reject(new Error("module failed: " + src)); };
			(document.body || document.head).appendChild(s);
		});
	}

	function ensureImportMap(importMap) {
		if (document.querySelector('script[type="importmap"]')) return;
		var map = importMap || global.__LEMMA_IMPORTMAP__;
		if (!map || typeof map !== "object") return;
		var s = document.createElement("script");
		s.type = "importmap";
		s.textContent = JSON.stringify(map);
		document.head.appendChild(s);
	}

	function readEmbeddedCode(opts) {
		if (opts && opts.code !== undefined) return opts.code;
		if (global.__LEMMA_CODE__ !== undefined) return global.__LEMMA_CODE__;
		var el = document.getElementById("lemma-code");
		if (el && el.textContent) {
			try {
				return JSON.parse(el.textContent);
			} catch (e) {
				console.error("lemmaPreviewUpgrade: bad #lemma-code JSON", e);
				return null;
			}
		}
		return null;
	}

	function afterPaint(fn) {
		if (typeof requestAnimationFrame === "function") {
			requestAnimationFrame(function () {
				requestAnimationFrame(fn);
			});
		} else {
			setTimeout(fn, 0);
		}
	}

	function waitFor(pred, timeoutMs, stepMs) {
		timeoutMs = timeoutMs == null ? 15000 : timeoutMs;
		stepMs = stepMs || 20;
		return new Promise(function (resolve, reject) {
			var t0 = Date.now();
			(function tick() {
				if (pred()) return resolve();
				if (Date.now() - t0 > timeoutMs) {
					return reject(new Error("lemmaPreviewUpgrade: wait timeout"));
				}
				setTimeout(tick, stepMs);
			})();
		});
	}

	function clearShell(replaceSelector) {
		var sel = replaceSelector || "#lemma-stage";
		var stage = document.querySelector(sel);
		if (stage && stage.parentNode) {
			stage.parentNode.removeChild(stage);
			return;
		}
		var shell = document.getElementById("lemma-shell");
		if (shell && shell.parentNode) shell.parentNode.removeChild(shell);
	}

	function sequence(list, fn) {
		var p = Promise.resolve();
		list.forEach(function (item) {
			p = p.then(function () { return fn(item); });
		});
		return p;
	}

	function shouldAutoStart() {
		if (global.__LEMMA_PREVIEW_UPGRADE_AUTO__ === false) return false;
		if (global.__LEMMA_CODE__ !== undefined) return true;
		if (document.getElementById("lemma-code")) return true;
		// true: PHP may place #lemma-code after this script; we re-check at start.
		return true;
	}

	/**
	 * Load full stack then mount Vue render app, replacing the preview shell.
	 * @param {object} [opts]
	 * @returns {Promise<*>}
	 */
	function lemmaPreviewUpgrade(opts) {
		opts = opts || {};
		if (global.__LEMMA_UPGRADED__) {
			return Promise.resolve(global.__LEMMA_UPGRADE_APP__);
		}
		if (global.__LEMMA_UPGRADING__) {
			return global.__LEMMA_UPGRADING__;
		}

		var v = assetV(opts);
		var code = readEmbeddedCode(opts);
		if (code === null && global.__LEMMA_PREVIEW_UPGRADE_AUTO__ !== true) {
			// No payload yet — stay silent unless forced.
			if (!opts.force) {
				return Promise.resolve(undefined);
			}
		}

		var work = Promise.resolve()
			.then(function () {
				return Promise.all(STYLES.map(function (href) {
					return loadCss(href).catch(function (err) {
						console.warn(err);
					});
				}));
			})
			.then(function () {
				return sequence(CLASSIC_SCRIPTS, loadClassicScript);
			})
			.then(function () {
				return sequence(
					["js/py.js?v=" + v, "js/std.js?v=" + v],
					loadClassicScript
				);
			})
			.then(function () {
				// Wait for katex (needed by utility.js latex helpers / Vue directives).
				var extras = DEFERRED_CLASSIC.map(function (src) {
					return loadClassicScript(src).catch(function (err) {
						console.warn(err);
					});
				});
				return Promise.all(extras);
			})
			.then(function () {
				ensureImportMap(opts.importMap);
				return loadModuleScript("js/utility.js");
			})
			.then(function () {
				return loadModuleScript("js/codemirrorBoot.js");
			})
			.then(function () {
				return waitFor(function () {
					return typeof global.createApp === "function" &&
						typeof global.Vue !== "undefined" &&
						global["vue3-sfc-loader"] &&
						global.cmBoot;
				}, 20000);
			})
			.then(function () {
				// Re-read in case JSON tag landed after first pass.
				if (code === null) code = readEmbeddedCode(opts);
				clearShell(opts.replaceSelector);
				var mountId = opts.mountId || "root";
				return global.createApp("render", code, mountId);
			})
			.then(function (app) {
				global.__LEMMA_UPGRADED__ = true;
				global.__LEMMA_UPGRADE_APP__ = app;
				global.__LEMMA_UPGRADING__ = null;
				return app;
			})
			.catch(function (err) {
				global.__LEMMA_UPGRADING__ = null;
				console.error("lemmaPreviewUpgrade failed", err);
				throw err;
			});

		global.__LEMMA_UPGRADING__ = work;
		return work;
	}

	global.lemmaPreviewUpgrade = lemmaPreviewUpgrade;

	if (shouldAutoStart()) {
		var start = function () {
			afterPaint(function () {
				// Only auto-run when a payload is present.
				if (readEmbeddedCode({}) === null && global.__LEMMA_PREVIEW_UPGRADE_AUTO__ !== true) {
					return;
				}
				lemmaPreviewUpgrade().catch(function () { /* logged above */ });
			});
		};
		if (document.readyState === "loading") {
			document.addEventListener("DOMContentLoaded", start, { once: true });
		} else {
			start();
		}
	}
})(typeof window !== "undefined" ? window : globalThis);
