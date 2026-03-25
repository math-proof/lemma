#!/usr/bin/env node
/**
 * Randomly sample `.lean` files under Lemma/ that are not yet in `test-lean-parser.mjs` CORPUS,
 * and keep those that pass parse + AST→String→AST jsonSerialize equality.
 *
 * Usage:
 *   node scripts/sample-round-trip-corpus.mjs [seed] [count]
 * Defaults: seed=20260324, count=12
 *
 * Prints JSON with `winners` (rel + note). Re-run with the same seed for a reproducible draw.
 */

import { readFileSync, readdirSync, statSync } from 'fs';
import { join, dirname, relative } from 'path';
import { fileURLToPath } from 'url';

import { compile } from '../static/js/parser/lean.js';

const __dirname = dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = join(__dirname, '..');

function stableAstJson(root) {
    return JSON.stringify(root.jsonSerialize(), (_k, v) => (typeof v === 'bigint' ? v.toString() : v));
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

/** `rel:` entries in CORPUS (same file; avoids exporting CORPUS from the test runner). */
function extractCorpusRels() {
    const txt = readFileSync(join(__dirname, 'test-lean-parser.mjs'), 'utf8');
    const rels = new Set();
    const re = /rel:\s*'([^']+)'/g;
    let m;
    while ((m = re.exec(txt)) !== null) {
        if (m[1].startsWith('Lemma/')) rels.add(m[1]);
    }
    return rels;
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

const seed = parseInt(process.argv[2] ?? '20260324', 10);
const want = parseInt(process.argv[3] ?? '12', 10);
const existing = extractCorpusRels();
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

console.log(
    JSON.stringify(
        {
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
