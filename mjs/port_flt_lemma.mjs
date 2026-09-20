/**
 * port_flt_lemma.mjs
 * ==================
 * Called from Python (flt_topo_sort.py) to parse an FLT solution file
 * with lean.js and return the theorem structure as JSON on stdout.
 *
 * Usage:  node mjs/port_flt_lemma.mjs <path-to-S_key.lean>
 * Output: JSON  { imports, namespace, theoremName, binders, conclusion, proof, key }
 */
import fs from 'fs';
import path from 'path';
import { parseTheoremFile } from '../static/js/parser/lean.js';

const filePath = process.argv[2];
if (!filePath) {
    console.error('Usage: node mjs/port_flt_lemma.mjs <path-to-S_key.lean>');
    process.exit(1);
}

// Derive the FLT key from the file name (`S_<key>.lean`).
const base = path.basename(filePath, '.lean');
const key = base.startsWith('S_') ? base.slice(2) : null;

const source = fs.readFileSync(filePath, 'utf8');
const result = parseTheoremFile(source, key);
if (!result) {
    console.error('parseTheoremFile returned null for: ' + filePath);
    process.exit(1);
}

console.log(JSON.stringify(result, null, 2));