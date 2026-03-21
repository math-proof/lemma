#!/usr/bin/env node
/**
 * Exercise `static/js/parser/lean.js` against inline smoke cases and real lemma files.
 *
 * Corpus paths must live under `Lemma/` — the same trees the site renders as lemmas.
 * (stdlib, sympy, etc. are excluded on purpose.)
 *
 * Usage:
 *   node scripts/test-lean-parser.mjs
 *   node scripts/test-lean-parser.mjs --strict
 *   node scripts/test-lean-parser.mjs --scan-lemma
 *   node scripts/test-lean-parser.mjs Lemma/Nat/Min.lean
 *   node scripts/test-lean-parser.mjs --json
 *
 * Exit codes:
 *   0 — all smoke tests passed; corpus is informational unless --strict
 *   1 — a smoke test failed, or --strict and a corpus file failed unexpectedly
 */

import { readFileSync, existsSync, readdirSync, statSync } from 'fs';
import { join, dirname, relative, isAbsolute } from 'path';
import { fileURLToPath } from 'url';

import { compile } from '../static/js/parser/lean.js';

const __dirname = dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = join(__dirname, '..');

/** Must always complete without throwing (regression guard). */
const SMOKE = [
    { name: 'trailing newline only', source: '\n' },
    { name: 'single import', source: 'import Foo\n' },
    { name: 'open', source: 'open Bar\n' },
    { name: 'two imports', source: 'import A\nimport B\n' },
];

/**
 * Lemma library files (under `Lemma/` only). Set `expectError` + `errorContains` when a file is
 * expected to fail until more of `php/parser/lean.php` is ported.
 */
const CORPUS = [
    { rel: 'Lemma/Nat/Min.lean', note: 'min_comm / parentheses' },
    { rel: 'Lemma/List/EqGetCons.lean', note: 'binders with commas' },
    {
        rel: 'Lemma/Tensor/GetSelect_1/eq/Cast_Get/of/Lt_Get_0/Lt_Get_1/GtLength_1.lean',
        note: 'deep proof / attrs',
    },
    { rel: 'Lemma/Bool/IffAndSAnd.lean', note: 'Bool' },
    { rel: 'Lemma/Bool/EqCast/of/SEq.lean', note: 'Bool / casts' },
    { rel: 'Lemma/Nat/Pow1/eq/One.lean', note: 'Nat' },
    { rel: 'Lemma/Int/Add/eq/Sub_Neg.lean', note: 'Int' },
    { rel: 'Lemma/Rat/EqDivMul.lean', note: 'Rat' },
    { rel: 'Lemma/Real/Pi/ne/Zero.lean', note: 'Real' },
    { rel: 'Lemma/Complex/Im/eq/MulAbs_SinArg.lean', note: 'Complex' },
    { rel: 'Lemma/Hyperreal/InfinitePosInfty.lean', note: 'Hyperreal' },
    { rel: 'Lemma/Set/UnionUnion.lean', note: 'Set' },
    { rel: 'Lemma/Finset/Ico/eq/SDiffRangeS.lean', note: 'Finset' },
    { rel: 'Lemma/List/EqDropAppend.lean', note: 'List' },
    { rel: 'Lemma/Vector/Eq_0/of/All_EqGet_0.lean', note: 'Vector' },
    { rel: 'Lemma/Tensor/EqLengthS.lean', note: 'Tensor' },
    // Extra diversity (stress different dirs / features; all expected to parse)
    { rel: 'Lemma/Nat/SubSub.lean', note: 'Nat Sub' },
    { rel: 'Lemma/Nat/MulMul.lean', note: 'Nat Mul' },
    { rel: 'Lemma/Nat/GeMax.lean', note: 'Nat max' },
    { rel: 'Lemma/Nat/EqMul1.lean', note: 'Nat EqMul1' },
    { rel: 'Lemma/Bool/Ite.lean', note: 'Bool Ite' },
    { rel: 'Lemma/Bool/ImpAndS/of/Imp.lean', note: 'Bool Imp' },
    { rel: 'Lemma/Finset/Inter.lean', note: 'Finset Inter' },
    { rel: 'Lemma/Finset/In_Union/is/OrInS.lean', note: 'Finset union' },
    { rel: 'Lemma/Finset/Sum/eq/Sum_MulBool.lean', note: 'Finset sum' },
    { rel: 'Lemma/Set/InterUnion/eq/UnionInterS.lean', note: 'Set inter/union' },
    { rel: 'Lemma/Rat/DivDiv/eq/Div_Mul.lean', note: 'Rat div' },
    { rel: 'Lemma/Rat/GeCeil.lean', note: 'Rat ceil' },
    { rel: 'Lemma/Real/LtExpS/is/Lt.lean', note: 'Real exp' },
    { rel: 'Lemma/Real/SinMul3/eq/SubMul3_Mul4SinMul3.lean', note: 'Real sin' },
    { rel: 'Lemma/Complex/ExpMulI/eq/AddCos_MulISin.lean', note: 'Complex exp' },
    { rel: 'Lemma/Hyperreal/NeInfty0.lean', note: 'Hyperreal ne' },
    { rel: 'Lemma/Int/AddSub/eq/SubAdd.lean', note: 'Int add/sub' },
    { rel: 'Lemma/Int/CeilSub/eq/SubCeil.lean', note: 'Int ceil' },
    { rel: 'Lemma/List/DropDrop/eq/Drop_Add.lean', note: 'List drop' },
    { rel: 'Lemma/List/Rotate_Mod/eq/Rotate.lean', note: 'List rotate' },
    { rel: 'Lemma/Vector/EqGetCons.lean', note: 'Vector cons' },
    { rel: 'Lemma/Vector/Map/eq/Cons_MapTail.lean', note: 'Vector map' },
    { rel: 'Lemma/Tensor/GetDot/eq/Sum_MulGetS.lean', note: 'Tensor dot' },
    { rel: 'Lemma/Tensor/GtLength_0.lean', note: 'Tensor length' },
];

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
    const out = { strict: false, json: false, scanLemma: false, extraFiles: [] };
    for (const a of argv) {
        if (a === '--help' || a === '-h') out.help = true;
        else if (a === '--strict') out.strict = true;
        else if (a === '--json') out.json = true;
        else if (a === '--scan-lemma') out.scanLemma = true;
        else if (!a.startsWith('-')) out.extraFiles.push(a);
    }
    return out;
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
  --strict       Exit 1 if any corpus file fails unexpectedly (smoke always enforced)
  --scan-lemma   After corpus, compile every file under Lemma/ and print ok/fail counts
  --json         Print machine-readable JSON on stdout
  --help         This message

Without paths, runs built-in smoke tests + corpus list. Extra paths must be under
Lemma/ (relative to repo root, or absolute inside the repo).
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

        corpusResults.push({
            file: label,
            tokens: source.length,
            lines: source.split('\n').length,
            ...expectation,
            ms: raw.ms,
            note: meta?.note,
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
        corpus: corpusResults,
        scanLemma: args.scanLemma ? scanResults : undefined,
        exitCode: strictFail ? 1 : 0,
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
    }

    process.exit(strictFail ? 1 : 0);
}

main();
