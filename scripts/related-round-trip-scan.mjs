#!/usr/bin/env node
/**
 * After fixing a round-trip bug and adding **one** verified row to `round-trip-corpus.jsonl`, run a
 * **type-specific scan**: find other `.lean` files under `Lemma/` that share the same parse/print shape
 * (same class of error), verify `parse → String(AST) → parse` with stable `jsonSerialize`, and append
 * all passing paths in one batch. Errors are often universal among similar sources; this avoids
 * rediscovering the same fix lemma-by-lemma.
 *
 * Workflow:
 *   1. Fix `static/js/parser/lean.js` (or parser input) and confirm one file round-trips.
 *   2. Pick the scan mode that matches the bug class (see MODES below).
 *   3. `node scripts/related-round-trip-scan.mjs <mode>` — review OK vs FAIL lists.
 *   4. `node scripts/related-round-trip-scan.mjs <mode> --append` — append OK rels not already in corpus.
 *   5. `node scripts/test-lean-parser.mjs` and `node scripts/build-round-trip-failures.mjs`.
 *
 * MODES:
 *   echo-def-module-proof — `Lean_def` / lemma with `LeanAssign` rhs an empty `LeanCaret`, proof as
 *     module-level siblings (comments + tactic). Matches the `LeanModule.toString` echo `:= by` tail.
 *   dangling-stc-tactic-block — module-level `LeanTactic` whose arg includes `LeanSequentialTacticCombinator`
 *     with empty `LeanCaret`, immediately followed by `LeanTacticBlock` (`constructor <;>` then `·`).
 *
 * Usage:
 *   node scripts/related-round-trip-scan.mjs
 *   node scripts/related-round-trip-scan.mjs echo-def-module-proof
 *   node scripts/related-round-trip-scan.mjs echo-def-module-proof --append
 */

import { readFileSync, readdirSync, statSync, appendFileSync } from 'fs';
import { join, dirname } from 'path';
import { fileURLToPath } from 'url';

import {
    compile,
    Lean_def,
    LeanAssign,
    LeanCaret,
    LeanTactic,
    LeanArgsSpaceSeparated,
    LeanSequentialTacticCombinator,
} from '../static/js/parser/lean.js';
import { loadRoundTripCorpusRels } from './load-round-trip-corpus.mjs';

const __dirname = dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = join(__dirname, '..');
const CORPUS_JSONL = join(__dirname, 'round-trip-corpus.jsonl');
const LEMMA_ROOT = join(REPO_ROOT, 'Lemma');

/** @type {Record<string, { note: string; test: (root: { args: unknown[] }) => boolean }>} */
const MODES = {
    'echo-def-module-proof': {
        note: 'echo `Lean_def` / module-level proof tail (`:= by` + siblings); see related-round-trip-scan.mjs',
        test(root) {
            const args = root.args;
            for (let i = 0; i < args.length; i++) {
                const a = args[i];
                if (!(a instanceof Lean_def)) continue;
                const asn = a.assignment;
                if (!(asn instanceof LeanAssign) || !(asn.rhs instanceof LeanCaret)) continue;
                let j = i + 1;
                while (j < args.length && args[j] instanceof LeanCaret) j++;
                while (j < args.length && args[j].is_comment?.()) j++;
                const proof = args[j];
                if (proof instanceof LeanTactic || proof instanceof LeanArgsSpaceSeparated) return true;
            }
            return false;
        },
    },
    'dangling-stc-tactic-block': {
        note: 'dangling `<;>` + module `LeanTacticBlock` merge in `LeanModule.toString` (scan tactic args from k=0)',
        test(root) {
            const args = root.args;
            for (let i = 0; i + 1 < args.length; i++) {
                const a = args[i];
                const n = args[i + 1];
                if (!(a instanceof LeanTactic) || n?.constructor?.name !== 'LeanTacticBlock') continue;
                for (let k = 0; k < a.args.length; k++) {
                    const x = a.args[k];
                    if (x instanceof LeanSequentialTacticCombinator && x.arg instanceof LeanCaret) return true;
                }
            }
            return false;
        },
    },
};

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

function stableAstJson(root) {
    return JSON.stringify(root.jsonSerialize(), (_k, v) => (typeof v === 'bigint' ? v.toString() : v));
}

function roundTripOk(source) {
    const r1 = compile(source);
    const r2 = compile(String(r1));
    return stableAstJson(r1) === stableAstJson(r2);
}

function relFromAbs(abs) {
    return abs.slice(REPO_ROOT.length + 1).split(/[/\\]/).join('/');
}

function main() {
    const argv = process.argv.slice(2).filter((a) => a !== '--append');
    const append = process.argv.includes('--append');

    if (argv.length === 0 || argv[0] === '-h' || argv[0] === '--help') {
        console.log(`Usage: node scripts/related-round-trip-scan.mjs <mode> [--append]\n\nModes:\n${Object.keys(MODES).map((k) => `  ${k}`).join('\n')}\n`);
        process.exit(0);
    }

    const mode = argv[0];
    const spec = MODES[mode];
    if (!spec) {
        console.error(`Unknown mode: ${mode}. Use: ${Object.keys(MODES).join(', ')}`);
        process.exit(1);
    }

    const corpus = loadRoundTripCorpusRels(CORPUS_JSONL);
    const files = walkLemmaLeanFiles(LEMMA_ROOT);
    const match = [];
    for (const abs of files) {
        const rel = relFromAbs(abs);
        if (corpus.has(rel)) continue;
        let root;
        try {
            root = compile(readFileSync(abs, 'utf8'));
        } catch {
            continue;
        }
        if (!spec.test(root)) continue;
        match.push(rel);
    }

    const ok = [];
    const bad = [];
    for (const rel of match) {
        const src = readFileSync(join(REPO_ROOT, rel), 'utf8');
        try {
            if (roundTripOk(src)) ok.push(rel);
            else bad.push(rel);
        } catch {
            bad.push(rel);
        }
    }

    console.log(`Mode: ${mode}`);
    console.log(`Off-corpus matches: ${match.length}; round-trip OK: ${ok.length}; still fail: ${bad.length}`);
    if (ok.length) console.log('OK:\n' + ok.map((r) => `  ${r}`).join('\n'));
    if (bad.length) console.log('FAIL (same shape, different bug):\n' + bad.map((r) => `  ${r}`).join('\n'));

    if (append && ok.length) {
        const lines = ok.map((rel) => JSON.stringify({ rel, note: spec.note }) + '\n').join('');
        appendFileSync(CORPUS_JSONL, lines, 'utf8');
        console.log(`Appended ${ok.length} line(s) to round-trip-corpus.jsonl`);
    } else if (append && ok.length === 0) {
        console.log('Nothing to append.');
    }
}

main();
