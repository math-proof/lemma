#!/usr/bin/env node
/**
 * Exercise `static/js/parser/lean.js` against inline smoke cases and real lemma files.
 *
 * Round-trip corpus paths live in `scripts/round-trip-corpus.jsonl` (one JSON object per line:
 * `{"rel":"Lemma/…","note":"…"}`). Paths must stay under `Lemma/` (same trees the site renders).
 *
 * Usage:
 *   node scripts/test-lean-parser.mjs
 *   node scripts/test-lean-parser.mjs --strict
 *   node scripts/test-lean-parser.mjs --scan-lemma
 *   node scripts/test-lean-parser.mjs Lemma/Nat/Min.lean
 *   node scripts/test-lean-parser.mjs --json
 *   node scripts/test-lean-parser.mjs --round-trip-verbose
 *
 * Exit codes:
 *   0 — all smoke tests passed; round-trip smoke + corpus rules satisfied; corpus parse informational unless --strict
 *   1 — a smoke test failed; or --strict and a corpus file failed unexpectedly; or an unexpected round-trip failure
 */

import { readFileSync, existsSync, readdirSync, statSync } from 'fs';
import { join, dirname, relative, isAbsolute } from 'path';
import { fileURLToPath } from 'url';

import { compile } from '../static/js/parser/lean.js';
import { loadRoundTripCorpus } from './load-round-trip-corpus.mjs';

const __dirname = dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = join(__dirname, '..');
const CORPUS_JSONL = join(__dirname, 'round-trip-corpus.jsonl');

/** Must always complete without throwing (regression guard). */
const SMOKE = [
    { name: 'trailing newline only', source: '\n' },
    { name: 'single import', source: 'import Foo\n' },
    { name: 'open', source: 'open Bar\n' },
    { name: 'two imports', source: 'import A\nimport B\n' },
];

/**
 * Corpus paths allowed to fail AST round-trip (`jsonSerialize` after parse → String → parse).
 * Keep empty so regressions fail CI; add paths only while fixing known parser/print gaps.
 */
const ROUND_TRIP_CORPUS_MISMATCH_OK = new Set([]);

/** Lemma paths and notes: `scripts/round-trip-corpus.jsonl` (one JSON object per line). */
const CORPUS = loadRoundTripCorpus(CORPUS_JSONL);

function resolveAbs(rel) {
    return isAbsolute(rel) ? rel : join(REPO_ROOT, rel);
}

/**
 * Walk `Lemma/` recursively; returns sorted `.lean` paths (for `--scan-lemma`).
 * Skips `*.echo.lean` (generated echo pipeline files, not source lemmas).
 */
function walkLemmaLeanFiles(dir) {
    const out = [];
    for (const name of readdirSync(dir)) {
        const p = join(dir, name);
        const st = statSync(p);
        if (st.isDirectory()) out.push(...walkLemmaLeanFiles(p));
        else if (name.endsWith('.lean') && !name.endsWith('.echo.lean')) out.push(p);
    }
    return out;
}

/** Resolved path must lie under `Lemma/` in the repo (lemmas for render). */
function isUnderLemma(absPath) {
    const label = relative(REPO_ROOT, absPath).replace(/\\/g, '/');
    return label.startsWith('Lemma/');
}

function parseArgs(argv) {
    const out = {
        strict: false,
        json: false,
        scanLemma: false,
        roundTripVerbose: false,
        extraFiles: [],
    };
    for (const a of argv) {
        if (a === '--help' || a === '-h') out.help = true;
        else if (a === '--strict') out.strict = true;
        else if (a === '--json') out.json = true;
        else if (a === '--scan-lemma') out.scanLemma = true;
        else if (a === '--round-trip' || a === '--round-trip-verbose') out.roundTripVerbose = true;
        else if (!a.startsWith('-')) out.extraFiles.push(a);
    }
    return out;
}

/**
 * Stable fingerprint for AST equality: `root.jsonSerialize()` then `JSON.stringify`
 * (handles nested structures; ignores object identity).
 *
 * @param {{ jsonSerialize: () => unknown }} root
 */
function stableAstJson(root) {
    return JSON.stringify(root.jsonSerialize(), (_k, v) => (typeof v === 'bigint' ? v.toString() : v));
}

/**
 * Stable round-trip: AST₁ = parse(source), text = String(AST₁), AST₂ = parse(text).
 * Returns whether `stableAstJson(AST₁) === stableAstJson(AST₂)` when both parses succeed.
 *
 * @param {string} source
 */
function runRoundTrip(source) {
    let root1;
    try {
        root1 = compile(source);
    } catch (e) {
        return {
            ok: false,
            phase: 'parse1',
            error: e instanceof Error ? e.message : String(e),
        };
    }
    const printed = String(root1);
    let root2;
    try {
        root2 = compile(printed);
    } catch (e) {
        return {
            ok: false,
            phase: 'parse2',
            printed,
            error: e instanceof Error ? e.message : String(e),
        };
    }
    const j1 = stableAstJson(root1);
    const j2 = stableAstJson(root2);
    return {
        ok: true,
        match: j1 === j2,
        printed,
        j1Len: j1.length,
        j2Len: j2.length,
    };
}

function runCompile(source, label) {
    const t0 = performance.now();
    try {
        const root = compile(source);
        const ms = Math.round(performance.now() - t0);
        return { ok: true, root, ms, label };
    } catch (err) {
        const ms = Math.round(performance.now() - t0);
        return {
            ok: false,
            error: err instanceof Error ? err.message : String(err),
            ms,
            label,
        };
    }
}

function checkExpectation(entry, result) {
    if (!entry.expectError) {
        return result.ok
            ? { status: 'pass', detail: `${result.ms}ms` }
            : { status: 'fail', detail: result.error };
    }
    if (result.ok) {
        return {
            status: 'unexpected-pass',
            detail: `parsed in ${result.ms}ms (expected throw; parser may have improved)`,
        };
    }
    if (entry.errorContains && !String(result.error).includes(entry.errorContains)) {
        return {
            status: 'fail',
            detail: `expected error containing ${JSON.stringify(entry.errorContains)}, got: ${result.error}`,
        };
    }
    return { status: 'expected-fail', detail: result.error };
}

function main() {
    const args = parseArgs(process.argv.slice(2));
    if (args.help) {
        console.log(`Usage: node scripts/test-lean-parser.mjs [options] [extra.lean ...]

Options:
  --strict                 Exit 1 if any corpus file fails unexpectedly (smoke always enforced)
  --scan-lemma             After corpus, compile every file under Lemma/ and print ok/fail counts
  --json                   Print machine-readable JSON on stdout
  --round-trip-verbose     Print per-file round-trip lines (default: summary only)
  --help                   This message

Every run checks: parse(s) → String(AST) → parse yields the same jsonSerialize() for all smoke
sources and for each corpus file (except paths listed in ROUND_TRIP_CORPUS_MISMATCH_OK).

Without paths, runs built-in smoke tests + corpus from scripts/round-trip-corpus.jsonl.
Extra paths must be under Lemma/ (relative to repo root, or absolute inside the repo).
`);
        process.exit(0);
    }

    const smokeResults = [];
    for (const s of SMOKE) {
        const r = runCompile(s.source, s.name);
        smokeResults.push({ name: s.name, ...r });
    }

    const smokeFailed = smokeResults.filter((r) => !r.ok);
    if (smokeFailed.length) {
        const payload = { smoke: smokeResults, error: 'smoke tests failed' };
        if (args.json) console.log(JSON.stringify(payload, null, 2));
        else {
            console.error('SMOKE TESTS FAILED');
            for (const r of smokeFailed) console.error(`  - ${r.label}: ${r.error}`);
        }
        process.exit(1);
    }

    /** @type {{ label: string; kind: string; match?: boolean; phase?: string; error?: string; j1Len?: number; j2Len?: number }[]} */
    const roundTripSmoke = [];
    for (const s of SMOKE) {
        const rt = runRoundTrip(s.source);
        roundTripSmoke.push({
            label: s.name,
            kind: 'smoke',
            ...(rt.ok
                ? { match: rt.match, j1Len: rt.j1Len, j2Len: rt.j2Len }
                : { phase: rt.phase, error: rt.error }),
        });
        if (!rt.ok || !rt.match) {
            if (!args.json) {
                console.error(`\nROUND-TRIP SMOKE FAILED: ${s.name}`);
                if (!rt.ok) console.error(`  phase=${rt.phase} ${rt.error}`);
                else console.error(`  jsonSerialize mismatch`);
            }
            process.exit(1);
        }
    }

    const filteredExtras = [];
    for (const rel of args.extraFiles) {
        const abs = resolveAbs(rel);
        if (!isUnderLemma(abs)) {
            console.warn(
                `[test-lean-parser] Skipping "${rel}" — only paths under Lemma/ are tested (lemmas for render).`,
            );
            continue;
        }
        filteredExtras.push(rel);
    }

    const corpusFiles = [...new Set([...CORPUS.map((c) => c.rel), ...filteredExtras])];
    const corpusResults = [];

    let roundTripFail = false;

    for (const rel of corpusFiles) {
        const abs = resolveAbs(rel);
        const label = relative(REPO_ROOT, abs).replace(/\\/g, '/');
        const meta = CORPUS.find((c) => c.rel === rel || c.rel === label);

        if (!label.startsWith('Lemma/')) {
            corpusResults.push({
                file: label,
                status: 'skip',
                detail: 'not under Lemma/',
            });
            continue;
        }

        if (!existsSync(abs)) {
            corpusResults.push({
                file: label,
                status: 'skip',
                detail: 'file not found',
            });
            continue;
        }

        const source = readFileSync(abs, 'utf8');
        const raw = runCompile(source, label);
        const expectation = meta
            ? checkExpectation(meta, raw)
            : raw.ok
              ? { status: 'pass', detail: `${raw.ms}ms` }
              : { status: 'fail', detail: raw.error };

        /** @type {Record<string, unknown> | null} */
        let roundTrip = null;
        if (raw.ok && expectation.status === 'pass') {
            const rt = runRoundTrip(source);
            const allowed = ROUND_TRIP_CORPUS_MISMATCH_OK.has(label);
            const bad = !rt.ok || !rt.match;
            if (bad && !allowed) roundTripFail = true;
            roundTrip = {
                match: rt.ok ? rt.match : false,
                phase: rt.ok ? undefined : rt.phase,
                error: rt.ok ? undefined : rt.error,
                j1Len: rt.ok ? rt.j1Len : undefined,
                j2Len: rt.ok ? rt.j2Len : undefined,
                allowedMismatch: allowed,
            };
        }

        corpusResults.push({
            file: label,
            tokens: source.length,
            lines: source.split('\n').length,
            ...expectation,
            ms: raw.ms,
            note: meta?.note,
            roundTrip,
        });
    }

    let strictFail = false;
    if (args.strict) {
        for (const c of corpusResults) {
            if (c.status === 'fail' || c.status === 'skip') strictFail = true;
        }
    }

    /** @type {{ file: string; ok: boolean; ms: number; error?: string }[]} */
    let scanResults = [];
    if (args.scanLemma) {
        const lemmaRoot = join(REPO_ROOT, 'Lemma');
        if (!existsSync(lemmaRoot)) {
            if (!args.json) console.warn('[test-lean-parser] Lemma/ not found; skipping --scan-lemma.');
        } else {
            const tScan = performance.now();
            const files = walkLemmaLeanFiles(lemmaRoot).sort();
            for (const abs of files) {
                const label = relative(REPO_ROOT, abs).replace(/\\/g, '/');
                const source = readFileSync(abs, 'utf8');
                const raw = runCompile(source, label);
                scanResults.push({
                    file: label,
                    ok: raw.ok,
                    ms: raw.ms,
                    ...(raw.ok ? {} : { error: raw.error }),
                });
                if (args.strict && !raw.ok) strictFail = true;
            }
            if (!args.json) {
                const ok = scanResults.filter((s) => s.ok).length;
                const fail = scanResults.length - ok;
                console.log(
                    `\nScan Lemma/ (${scanResults.length} files, ${Math.round(performance.now() - tScan)}ms): ${ok} ok, ${fail} fail`,
                );
                if (fail > 0) {
                    let n = 0;
                    for (const s of scanResults) {
                        if (s.ok) continue;
                        console.log(`  FAIL ${s.file}\n         ${s.error}`);
                        if (++n >= 25) {
                            console.log(`  ... (${fail - n} more failed)`);
                            break;
                        }
                    }
                }
            }
        }
    }

    const summary = {
        smoke: smokeResults.map((r) => ({
            name: r.label,
            ok: r.ok,
            ms: r.ms,
            root: r.root?.constructor?.name,
        })),
        roundTripSmoke,
        corpus: corpusResults,
        scanLemma: args.scanLemma ? scanResults : undefined,
        exitCode: strictFail || roundTripFail ? 1 : 0,
    };

    if (args.json) {
        console.log(JSON.stringify(summary, null, 2));
    } else {
        console.log('Lean parser smoke tests (lean.js)\n');
        for (const r of smokeResults) {
            console.log(`  OK  ${r.label}  (${r.ms}ms)  → ${r.root?.constructor?.name ?? 'n/a'}`);
        }

        console.log('\nCorpus (real .lean files)\n');
        for (const c of corpusResults) {
            const flag =
                c.status === 'pass' || c.status === 'expected-fail' || c.status === 'unexpected-pass'
                    ? c.status === 'pass' || c.status === 'unexpected-pass'
                        ? 'OK '
                        : 'XF '
                    : 'FAIL';
            console.log(
                `  ${flag} ${c.file}  [${c.status}] ${c.detail}${c.note ? `  (${c.note})` : ''}`,
            );
        }

        if (args.strict && strictFail) {
            console.error('\n--strict: one or more corpus/scan entries failed or were missing.');
        } else if (!args.strict) {
            console.log(
                '\nNote: expected failures (XF) match known missing PHP ports in lean.js. Re-run with --strict to fail on any corpus error.',
            );
        }

        const rtCorpus = corpusResults.filter((c) => c.roundTrip);
        const rtOk = rtCorpus.filter((c) => c.roundTrip.match === true).length;
        const rtAllow = rtCorpus.filter(
            (c) => c.roundTrip && c.roundTrip.allowedMismatch && c.roundTrip.match !== true,
        ).length;
        console.log(
            `\nRound-trip (parse → String(AST) → parse; same jsonSerialize): smoke OK (${SMOKE.length}/${SMOKE.length}). Corpus checked: ${rtCorpus.length} — ${rtOk} match, ${rtAllow} allowlisted mismatch (ROUND_TRIP_CORPUS_MISMATCH_OK).`,
        );
        if (args.roundTripVerbose) {
            for (const c of rtCorpus) {
                const rt = c.roundTrip;
                if (rt.match === true) console.log(`  RT OK   ${c.file}`);
                else if (rt.allowedMismatch)
                    console.log(
                        `  RT XF   ${c.file}  (${rt.phase ?? 'mismatch'}${rt.error ? `: ${rt.error}` : ` len ${rt.j1Len} vs ${rt.j2Len}`})`,
                    );
                else
                    console.log(
                        `  RT FAIL ${c.file}  (${rt.phase ?? 'mismatch'}${rt.error ? `: ${rt.error}` : ''})`,
                    );
            }
        }
        if (roundTripFail) {
            console.error(
                '\nRound-trip: unexpected failure (not in ROUND_TRIP_CORPUS_MISMATCH_OK). Use --round-trip-verbose.',
            );
        }
    }

    process.exit(strictFail || roundTripFail ? 1 : 0);
}

main();
