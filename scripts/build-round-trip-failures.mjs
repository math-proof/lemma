#!/usr/bin/env node
/**
 * Build `scripts/round-trip-failures.jsonl`: every `Lemma/*.lean` (excluding `*.echo.lean`)
 * that is **not** listed in `scripts/round-trip-corpus.jsonl` and fails either initial `compile`
 * or AST → string → AST with stable `toJSON` (same rules as `test-lean-parser.mjs`).
 *
 * After extending the corpus for a fix, run `related-round-trip-scan.mjs` (same error shape) before
 * relying only on this full-file list.
 *
 * Usage: node scripts/build-round-trip-failures.mjs
 */

import { readFileSync, writeFileSync, existsSync, readdirSync, statSync } from 'fs';
import { join, dirname, relative } from 'path';
import { fileURLToPath } from 'url';

import { compile } from '../static/js/parser/lean.js';
import { loadRoundTripCorpus } from './load-round-trip-corpus.mjs';

const __dirname = dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = join(__dirname, '..');
const CORPUS_JSONL = join(__dirname, 'round-trip-corpus.jsonl');
const OUT_JSONL = join(__dirname, 'round-trip-failures.jsonl');

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
    return JSON.stringify(root.toJSON(), (_k, v) => (typeof v === 'bigint' ? v.toString() : v));
}

/**
 * @param {string} source
 * @returns {Record<string, unknown> | null} failure object, or null if this file would pass round-trip
 */
function analyzeOffCorpusFile(source) {
    let root1;
    try {
        root1 = compile(source);
    } catch (e) {
        return {
            failure: 'parse1',
            error: e instanceof Error ? e.message : String(e),
        };
    }
    const printed = String(root1);
    let root2;
    try {
        root2 = compile(printed);
    } catch (e) {
        return {
            failure: 'parse2',
            error: e instanceof Error ? e.message : String(e),
            printedLength: printed.length,
            printedHead: printed.slice(0, 400),
        };
    }
    const j1 = stableAstJson(root1);
    const j2 = stableAstJson(root2);
    if (j1 !== j2) {
        return {
            failure: 'mismatch',
            j1Len: j1.length,
            j2Len: j2.length,
        };
    }
    return null;
}

function main() {
    if (!existsSync(CORPUS_JSONL)) {
        console.error(`Missing ${CORPUS_JSONL}`);
        process.exit(1);
    }
    const lemmaRoot = join(REPO_ROOT, 'Lemma');
    if (!existsSync(lemmaRoot)) {
        console.error(`Missing ${lemmaRoot}`);
        process.exit(1);
    }

    const inCorpus = new Set(loadRoundTripCorpus(CORPUS_JSONL).map((r) => r.rel));
    const absAll = walkLemmaLeanFiles(lemmaRoot);
    const rows = [];

    for (const abs of absAll) {
        const rel = relative(REPO_ROOT, abs).replace(/\\/g, '/');
        if (inCorpus.has(rel)) continue;
        const source = readFileSync(abs, 'utf8');
        const f = analyzeOffCorpusFile(source);
        if (f) rows.push({ rel, ...f });
    }

    rows.sort((a, b) => a.rel.localeCompare(b.rel));

    const header =
        '# Off-corpus round-trip failures — not in round-trip-corpus.jsonl; fail parse1, parse2, or toJSON match after print. Regenerate: node scripts/build-round-trip-failures.mjs';
    const body = rows.map((r) => JSON.stringify(r)).join('\n') + (rows.length ? '\n' : '');
    writeFileSync(OUT_JSONL, `${header}\n${body}`, 'utf8');

    const byFail = { parse1: 0, parse2: 0, mismatch: 0 };
    for (const r of rows) {
        const k = r.failure;
        if (k in byFail) byFail[k]++;
    }

    console.log(
        JSON.stringify(
            {
                output: relative(REPO_ROOT, OUT_JSONL).replace(/\\/g, '/'),
                failures: rows.length,
                byFailure: byFail,
                lemmaSourceFiles: absAll.length,
                inCorpus: inCorpus.size,
            },
            null,
            2,
        ),
    );
}

main();
