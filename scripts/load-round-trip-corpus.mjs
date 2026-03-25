/**
 * Load AST round-trip corpus: one JSON object per line.
 * Each line: { "rel": "Lemma/…/file.lean", "note": "optional" }
 * Blank lines and lines starting with # are ignored.
 */
import { readFileSync, existsSync } from 'fs';

/**
 * @param {string} jsonlPath absolute path to .jsonl
 * @returns {{ rel: string; note?: string; expectError?: boolean; errorContains?: string }[]}
 */
export function loadRoundTripCorpus(jsonlPath) {
    if (!existsSync(jsonlPath)) {
        throw new Error(`Round-trip corpus not found: ${jsonlPath}`);
    }
    const raw = readFileSync(jsonlPath, 'utf8');
    const out = [];
    let lineNo = 0;
    for (const line of raw.split(/\r?\n/)) {
        lineNo++;
        const t = line.trim();
        if (!t || t.startsWith('#')) continue;
        let row;
        try {
            row = JSON.parse(t);
        } catch (e) {
            throw new Error(`${jsonlPath}:${lineNo}: invalid JSON: ${e instanceof Error ? e.message : e}`);
        }
        if (!row || typeof row.rel !== 'string') {
            throw new Error(`${jsonlPath}:${lineNo}: each row must have string "rel"`);
        }
        if (!row.rel.startsWith('Lemma/')) {
            throw new Error(`${jsonlPath}:${lineNo}: rel must start with Lemma/: ${row.rel}`);
        }
        out.push(row);
    }
    return out;
}

/**
 * @param {string} jsonlPath
 * @returns {Set<string>} rel paths
 */
export function loadRoundTripCorpusRels(jsonlPath) {
    return new Set(loadRoundTripCorpus(jsonlPath).map((r) => r.rel));
}
