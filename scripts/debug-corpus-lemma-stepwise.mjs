#!/usr/bin/env node
/**
 * Step-by-step parse → print → re-parse for one corpus lemma (translation sanity).
 *
 * Easiest corpus file (when no path given): minimum line count, then byte size.
 *
 * Usage:
 *   node scripts/debug-corpus-lemma-stepwise.mjs
 *   node scripts/debug-corpus-lemma-stepwise.mjs Lemma/.../file.lean
 */
import { readFileSync } from 'fs';
import { join } from 'path';
import { compile } from '../static/js/parser/lean.js';
import { loadRoundTripCorpus } from './load-round-trip-corpus.mjs';

function easiestCorpusRel() {
    const rows = loadRoundTripCorpus(join(process.cwd(), 'scripts/round-trip-corpus.jsonl'));
    const stats = rows.map((r) => {
        const s = readFileSync(join(process.cwd(), r.rel), 'utf8');
        return { rel: r.rel, lines: s.split('\n').length, bytes: s.length };
    });
    stats.sort((a, b) => a.lines - b.lines || a.bytes - b.bytes);
    return stats[0];
}

let rel = process.argv[2];
if (!rel) {
    const e = easiestCorpusRel();
    console.log(
        `=== Step 0: Easiest corpus lemma (min lines, then bytes) ===\n${e.rel}  (${e.lines} lines, ${e.bytes} bytes)\n`,
    );
    rel = e.rel;
}

const source = readFileSync(join(process.cwd(), rel), 'utf8');

function stableAstJson(root) {
    return JSON.stringify(root.jsonSerialize(), (_, v) => (typeof v === 'bigint' ? v.toString() : v));
}

function brief(n, depth = 0, maxDepth = 8) {
    if (!n || depth > maxDepth) return;
    const pad = '  '.repeat(depth);
    let t = n.constructor.name;
    if (n.tacticName) t += ` [${n.tacticName}]`;
    if (n.text != null && String(n.text).length < 40) t += ` <${n.text}>`;
    console.log(pad + t);
    // Walk `args` only: `lhs`/`rhs`/`arg` mirror `args` on LeanBinary/LeanUnary and would duplicate.
    if (n.args) for (const c of n.args) brief(c, depth + 1, maxDepth);
}

console.log(`=== Step 1: Source (${rel}) ===\n${source}\n`);

console.log('=== Step 2: Parse (compile) ===');
const root = compile(source);
console.log(`root: ${root.constructor.name}, top-level args: ${root.args.length}\n`);
brief(root, 0);

console.log('\n=== Step 3: Print (String(AST)) ===');
const printed = String(root);
console.log(printed);

console.log('\n=== Step 4: Re-parse printed ===');
const root2 = compile(printed);
const m = stableAstJson(root) === stableAstJson(root2);
console.log(`stable jsonSerialize match: ${m}`);
if (!m) {
    const j1 = stableAstJson(root);
    const j2 = stableAstJson(root2);
    let i = 0;
    while (i < j1.length && j1[i] === j2[i]) i++;
    console.log(`first diff at char ${i}`);
    console.log('j1:', j1.slice(i, i + 160));
    console.log('j2:', j2.slice(i, i + 160));
}
