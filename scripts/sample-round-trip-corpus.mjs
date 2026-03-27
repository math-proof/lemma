#!/usr/bin/env node
/**
 * Randomly sample `.lean` files under Lemma/ that are not yet in `round-trip-corpus.jsonl`,
 * and keep those that pass parse + AST→String→AST toJSON equality.
 *
 * Usage:
 *   node scripts/sample-round-trip-corpus.mjs [seed] [count]
 *   node scripts/sample-round-trip-corpus.mjs [seed] [count] --append
 * Defaults: seed=20260324, count=12
 *
 * With --append: appends winner lines to scripts/round-trip-corpus.jsonl (skips rels already listed).
 * Without --append: prints JSON only (rel + note) for manual copy.
 *
 * For a **known bug class** (not random sampling), prefer `related-round-trip-scan.mjs` after each fix:
 * type-specific detectors batch-append every passing lemma that shares the same parse shape.
 */

import { readFileSync, readdirSync, statSync, appendFileSync, existsSync } from 'fs';
import { join, dirname, relative } from 'path';
import { fileURLToPath } from 'url';

import { compile } from '../static/js/parser/lean.js';
import { loadRoundTripCorpusRels } from './load-round-trip-corpus.mjs';

const __dirname = dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = join(__dirname, '..');
const CORPUS_JSONL = join(__dirname, 'round-trip-corpus.jsonl');

function stableAstJson(root) {
    return JSON.stringify(root.toJSON(), (_k, v) => (typeof v === 'bigint' ? v.toString() : v));
}

function roundTripOk(source) {
    const root1 = compile(source);
    const printed = String(root1);
    const root2 = compile(printed);
    return stableAstJson(root1) === stableAstJson(root2);
}

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

function mulberry32(a) {
    return function () {
        let t = (a += 0x6d2b79f5);
        t = Math.imul(t ^ (t >>> 15), t | 1);
        t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
        return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
}

function shuffle(arr, rand) {
    const a = [...arr];
    for (let i = a.length - 1; i > 0; i--) {
        const j = Math.floor(rand() * (i + 1));
        [a[i], a[j]] = [a[j], a[i]];
    }
    return a;
}

const argv = process.argv.slice(2);
const append = argv.includes('--append');
const nums = argv.filter((a) => /^\d+$/.test(a));
const seed = parseInt(nums[0] ?? '20260324', 10);
const want = parseInt(nums[1] ?? '12', 10);

const existing = existsSync(CORPUS_JSONL)
    ? loadRoundTripCorpusRels(CORPUS_JSONL)
    : new Set();

const absAll = walkLemmaLeanFiles(join(REPO_ROOT, 'Lemma'));
const candidates = absAll
    .map((abs) => relative(REPO_ROOT, abs).replace(/\\/g, '/'))
    .filter((rel) => !existing.has(rel));

const rand = mulberry32(seed >>> 0);
const shuffled = shuffle(candidates, rand);
const winners = [];
let tried = 0;
for (const rel of shuffled) {
    if (winners.length >= want) break;
    tried++;
    const abs = join(REPO_ROOT, rel);
    let src;
    try {
        src = readFileSync(abs, 'utf8');
        compile(src);
    } catch {
        continue;
    }
    try {
        if (!roundTripOk(src)) continue;
    } catch {
        continue;
    }
    const top = rel.split('/')[1] ?? 'Lemma';
    winners.push({ rel, note: `random sample (${top})` });
}

if (append && winners.length > 0) {
    const lines = winners.map((w) => JSON.stringify(w)).join('\n') + '\n';
    appendFileSync(CORPUS_JSONL, lines, 'utf8');
}

console.log(
    JSON.stringify(
        {
            corpusFile: relative(REPO_ROOT, CORPUS_JSONL).replace(/\\/g, '/'),
            append,
            seed,
            want,
            candidatesPool: candidates.length,
            triedUntilDone: tried,
            added: winners.length,
            winners,
        },
        null,
        2,
    ),
);
