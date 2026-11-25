/**
 * Persist one Echo compile: the lemma row, docstring rows, and fingerprints.
 * Proof fingerprints are `expr.toJson` of the expression `expr.toLatex` printed.
 * Given and imply stay on the source-syntax trees.
 */
import { lemmaSearchDocuments } from '../lemmaPath.mjs';
import { writeLemmaIndex } from '../leanInvertedIndex.mjs';
import { structToFingerprint } from './structToFingerprint.mjs';
import { peelDocstrings, replaceDocstrings } from './fetchLemmaMysql.mjs';

function jsonCol(v) {
  return JSON.stringify(v ?? (Array.isArray(v) ? [] : {}));
}

function echoProofSteps(lem) {
  const proof = lem?.proof;
  if (Array.isArray(proof)) return proof;
  if (proof && typeof proof === 'object') {
    if (Array.isArray(proof.by)) return proof.by;
    if (Array.isArray(proof.calc)) return proof.calc;
  }
  return [];
}

/** Every `expr.toJson` on a step. Several echoes on one line arrive as an array. */
function echoStructs(struct) {
  const list = Array.isArray(struct) ? struct : [struct];
  return list.filter((item) => item && typeof item === 'object' && !Array.isArray(item));
}

/**
 * Proof fingerprints from Echo. Returns null when no step carried a struct,
 * so the caller keeps the source-syntax proof documents.
 */
export function proofDocumentsFromEcho(lemmas) {
  const docs = [];
  let any = false;
  (lemmas ?? []).forEach((lem, lemmaId) => {
    echoProofSteps(lem).forEach((step, latexId) => {
      const trees = [];
      for (const struct of echoStructs(step?.struct)) {
        try {
          const json = structToFingerprint(struct);
          if (json != null && json !== '') trees.push(json);
        } catch {
          /* skip a struct this converter cannot read */
        }
      }
      if (!trees.length) return;
      any = true;
      docs.push({
        json: trees.length === 1 ? trees[0] : trees,
        lemmaId,
        section: 'proof',
        latexId,
      });
    });
  });
  return any ? docs : null;
}

/** Drop `expr.toJson` from the payload. The fingerprint table keeps the tree. */
export function stripEchoStructs(lemmas) {
  for (const lem of lemmas ?? []) {
    for (const step of echoProofSteps(lem)) {
      if (step && typeof step === 'object') delete step.struct;
    }
  }
}

/**
 * Replace the lemma row and its fingerprints. `code.lemma` proof steps must
 * still carry `struct` from Echo; this strips those fields before returning.
 * The caller owns `conn` and must not be inside a transaction.
 */
export async function replaceLemmaRow(conn, module, code, abs, startedAt) {
  const errs = Array.isArray(code.error) ? code.error : [];
  let fingerprint = null;
  let documents = null;
  try {
    if (abs) {
      const extracted = lemmaSearchDocuments(abs);
      fingerprint = extracted.fingerprint;
      documents = extracted.documents;
    }
  } catch {
    fingerprint = null;
    documents = null;
  }
  const meta = {};
  if (errs.length) meta.error = errs;
  const metaJson = Object.keys(meta).length ? JSON.stringify(meta) : null;
  const peeled = peelDocstrings(code.lemma ?? []);
  const echoProof = proofDocumentsFromEcho(peeled.lemmas);
  if (echoProof) {
    documents = (documents ?? []).filter((doc) => doc.section !== 'proof').concat(echoProof);
  }
  stripEchoStructs(peeled.lemmas);

  const fields = [
    jsonCol(code.imports ?? []),
    jsonCol(code.open ?? []),
    jsonCol(code.set_option ?? []),
    jsonCol(code.preamble ?? []),
    jsonCol(peeled.lemmas),
    metaJson,
    jsonCol(code.date ?? {}),
  ];

  // UNIQUE `uq_lemma_module (module)` keeps `id` stable: UPDATE the existing
  // row in place. INSERT only when the module is new, so inverted postings
  // are not orphaned by a new AUTO_INCREMENT id. The row lock and the
  // fingerprint/postings write share one transaction: a reader sees either
  // the previous revision or the new one, never a half-applied state.
  await conn.beginTransaction();
  try {
    const [existing] = await conn.query(
      "SELECT id, JSON_EXTRACT(meta, '$.revision') AS revision FROM lemma WHERE module = ? FOR UPDATE",
      [module],
    );
    let id;
    if (existing.length) {
      id = existing[0].id;
      // An older job may acquire the lock after a newer build already won.
      if (Number(existing[0].revision ?? 0) > Number(startedAt)) {
        await conn.rollback();
        return { id, stale: true };
      }
      await conn.query(
        `UPDATE lemma
         SET imports = CAST(? AS JSON),
             \`open\` = CAST(? AS JSON),
             set_option = CAST(? AS JSON),
             preamble = CAST(? AS JSON),
             lemma = CAST(? AS JSON),
             meta = CAST(? AS JSON),
             date = CAST(? AS JSON)
         WHERE id = ?`,
        [...fields, id],
      );
    } else {
      const [result] = await conn.query(
        `INSERT INTO lemma
          (module, imports, \`open\`, set_option, preamble, lemma, meta, date)
         VALUES (?, CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON))`,
        [module, ...fields],
      );
      id = result.insertId;
    }

    const { postings } = await writeLemmaIndex(conn, {
      id,
      module,
      json: fingerprint,
      documents,
      startedAt,
    });
    await replaceDocstrings(conn, id, peeled.rows);
    await conn.commit();
    return { id, postings };
  } catch (err) {
    await conn.rollback();
    throw err;
  }
}
