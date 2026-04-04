#!/usr/bin/env node
/**
 * Compare lemma payload from PHP (localhost) vs Node (localhost:3000).
 * Requires both servers to be running.
 *
 * Usage:
 *   node scripts/compare-php-node.mjs [module]
 */

import path from 'path';
import fs from 'fs';
import http from 'http';
import { fileURLToPath } from 'url';
import { REPO_ROOT } from '../server/lean/modulePath.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const MODULE = process.argv[2] || 'Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax';

const IGNORE_PATHS = new Set([
  'user', // lean.php vs lean deployment-specific
  'set_option', // PHP string vs Node object; structural
  'lemma.0.imply.lean', // brace/whitespace formatting differences
  'lemma.0.proof', // PHP object vs Node array
  'error', 'error.0', // PHP runs Lean linter; Node does not
]);

function compare(a, b, keyPath = '') {
  if (IGNORE_PATHS.has(keyPath)) return [];
  const diffs = [];
  if (typeof a !== typeof b) {
    diffs.push({ path: keyPath, a: typeof a, b: typeof b });
    return diffs;
  }
  if (a === null || b === null) {
    if (a !== b) diffs.push({ path: keyPath, a, b });
    return diffs;
  }
  if (typeof a !== 'object') {
    if (a !== b) diffs.push({ path: keyPath, a, b });
    return diffs;
  }
  if (Array.isArray(a) !== Array.isArray(b)) {
    diffs.push({
      path: keyPath,
      a: Array.isArray(a) ? 'array' : 'object',
      b: Array.isArray(b) ? 'array' : 'object',
    });
    return diffs;
  }
  const keys = new Set([...Object.keys(a), ...Object.keys(b)]);
  for (const k of keys) {
    const p = keyPath ? `${keyPath}.${k}` : k;
    if (IGNORE_PATHS.has(p)) continue;
    if (!(k in a)) diffs.push({ path: p, a: undefined, b: b[k] });
    else if (!(k in b)) diffs.push({ path: p, a: a[k], b: undefined });
    else diffs.push(...compare(a[k], b[k], p));
  }
  return diffs;
}

/** Extract createApp('render', {...}) from HTML. */
function extractPayload(html) {
  const marker = "createApp('render', ";
  const idx = html.indexOf(marker);
  if (idx < 0) return null;
  let start = idx + marker.length;
  let depth = 0;
  let inStr = false;
  let i = start;
  for (; i < html.length; i++) {
    const c = html[i];
    if (inStr) {
      if (c === '\\' && i + 1 < html.length) {
        i++;
        continue;
      }
      if (c === '"') {
        let backs = 0;
        for (let j = i - 1; j >= start && html[j] === '\\'; j--) backs++;
        if (backs % 2 === 0) inStr = false;
      }
      continue;
    }
    if (c === '"') {
      inStr = true;
      continue;
    }
    if (c === '{') depth++;
    else if (c === '}') {
      depth--;
      if (depth === 0) break;
    }
  }
  for (let end = i; end <= Math.min(i + 10, html.length); end++) {
    const raw = html.slice(start, end);
    try {
      return JSON.parse(raw);
    } catch (_) {}
  }
  const raw = html.slice(start, i);
  if (process.env.DEBUG_COMPARE) {
    fs.writeFileSync(path.join(REPO_ROOT, '_compare_debug.json'), raw, 'utf8');
    console.error('Debug: wrote raw extract to _compare_debug.json');
  }
  throw new Error(`JSON parse failed at position ${i}`);
}

function fetch(url) {
  return new Promise((resolve, reject) => {
    http
      .get(url, { timeout: 15000 }, (res) => {
        const chunks = [];
        res.on('data', (c) => chunks.push(c));
        res.on('end', () => resolve(Buffer.concat(chunks).toString('utf8')));
      })
      .on('error', reject);
  });
}

async function main() {
  const phpUrl = `http://localhost:8080/lean.php/?module=${encodeURIComponent(MODULE)}`;
  const nodeUrl = `http://localhost:3000/lean/?module=${encodeURIComponent(MODULE)}`;
  console.log('Fetching from URLs...');
  console.log('  PHP:  ', phpUrl);
  console.log('  Node: ', nodeUrl);
  try {
    const [phpHtml, nodeHtml] = await Promise.all([fetch(phpUrl), fetch(nodeUrl)]);
    const phpPayload = extractPayload(phpHtml);
    const nodePayload = extractPayload(nodeHtml);

    const diffs = compare(phpPayload, nodePayload);

    const phpExplicit = phpPayload?.lemma?.[0]?.explicit;
    const nodeExplicit = nodePayload?.lemma?.[0]?.explicit;
    const phpGiven = phpPayload?.lemma?.[0]?.given;
    const nodeGiven = nodePayload?.lemma?.[0]?.given;
    const explicitMatch = phpExplicit === nodeExplicit;
    const givenMatch = JSON.stringify(phpGiven) === JSON.stringify(nodeGiven);

    if (diffs.length === 0) {
      console.log('PASS: payloads are exactly the same');
      process.exit(0);
    }

    console.log('DIFF: payloads differ');
    console.log('');
    console.log('Given section (lemma[0].explicit):');
    console.log(explicitMatch ? '  MATCH' : '  DIFFER (PHP vs Node)');
    if (!explicitMatch) {
      console.log('  PHP: ', JSON.stringify(phpExplicit));
      console.log('  Node:', JSON.stringify(nodeExplicit));
    }
    console.log('lemma[0].given:', givenMatch ? 'MATCH' : 'DIFFER');
    console.log('');
    const maxShow = 25;
    for (let i = 0; i < Math.min(diffs.length, maxShow); i++) {
      const d = diffs[i];
      const trunc = (v) => {
        const s = typeof v === 'string' && v.length > 70 ? v.slice(0, 70) + '...' : v;
        return JSON.stringify(s);
      };
      console.log(`  ${d.path}`);
      console.log(`    PHP:  ${trunc(d.a)}`);
      console.log(`    Node: ${trunc(d.b)}`);
    }
    if (diffs.length > maxShow) {
      console.log(`  ... and ${diffs.length - maxShow} more`);
    }
    process.exit(1);
  } catch (e) {
    console.error('Fetch failed:', e.message);
    process.exit(1);
  }
}

main();
