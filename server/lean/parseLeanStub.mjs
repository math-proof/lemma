/**
 * Best-effort Lean → `render.vue` props without the PHP `compile` / `render2vue` pipeline.
 * Uses structure comments (`-- imply`, `-- proof`, `-- given`) and `lemma` headers.
 * Full KaTeX / tactic LaTeX (PHP `toLatex`) is not replicated; we emit a safe KaTeX
 * fallback so `v-latex.block` runs (same layout as PHP) instead of `imply.insert` +
 * CodeMirror-only for the imply section.
 */

/** Escape a single line for use inside `\text{...}` in KaTeX. */
export function escapeLatexText(s) {
  return String(s)
    .replace(/\\/g, '\\textbackslash{}')
    .replace(/\{/g, '\\{')
    .replace(/\}/g, '\\}')
    .replace(/\$/g, '\\$')
    .replace(/&/g, '\\&')
    .replace(/#/g, '\\#')
    .replace(/\^/g, '\\textasciicircum{}')
    .replace(/_/g, '\\_')
    .replace(/%/g, '\\%')
    .replace(/~/g, '\\textasciitilde{}');
}

function lineIndent(line) {
  const m = String(line).match(/^\s*/);
  return m ? m[0].length : 0;
}

/**
 * Best-effort label for a proof step (PHP uses these in `\tag*{…}` on the right).
 * Uses only the first line of a multi-line tactic.
 */
export function extractProofStepTag(firstLine) {
  const t = String(firstLine).trim();
  let m = t.match(/^denote\s+([^\s:]+?)\s*:/u);
  if (m) return m[1];
  m = t.match(/^have\s+([^\s]+?)\s*:=/u);
  if (m) return m[1];
  m = t.match(/^intro\s+(\S+)/u);
  if (m) return m[1];
  m = t.match(/^obtain\s+([^\s]+?)\s*:=/u);
  if (m) return m[1];
  return null;
}

/**
 * Monospace-style display of Lean source via KaTeX (not semantic math like PHP `toLatex`).
 * Renders as a left-aligned `aligned` block so it matches the block layout of real LaTeX.
 * Optional `tag` (or auto-detect from first line) adds a right `\tag*{…}` like PHP.
 */
export function leanToFallbackLatex(lean, options = {}) {
  if (!lean || !String(lean).trim()) return '';
  const lines = String(lean).split('\n').filter((l) => l.length > 0);
  if (!lines.length) return '';
  const tag =
    options.tag !== undefined && options.tag !== null && options.tag !== ''
      ? options.tag
      : extractProofStepTag(lines[0]);
  const n = lines.length;
  const rows = lines
    .map((line, i) => {
      const isLast = i === n - 1;
      const row = `&\\text{${escapeLatexText(line)}}`;
      if (isLast && tag) {
        /** `\tag*` must stay inside `aligned` — KaTeX rejects `\end{aligned}\tag*{…}`. */
        return `${row}\\tag*{\\text{${escapeLatexText(tag)}}}`;
      }
      return row;
    })
    .join('\\\\');
  return `\\begin{aligned}${rows}\\end{aligned}`;
}

export function buildRenderPropsFromSource(source, module, { user = 'lean' } = {}) {
  const lines = source.replace(/\r\n/g, '\n').split('\n');
  const imports = [];
  const openParts = [];
  let i = 0;
  while (i < lines.length) {
    const t = lines[i].trim();
    if (t.startsWith('import ')) imports.push(t.slice('import '.length).trim());
    else if (t.startsWith('open ')) {
      const rest = t.slice('open '.length).trim();
      openParts.push(rest.split(/\s+/).filter(Boolean));
    } else break;
    i++;
  }

  const afterImports = lines.slice(i).join('\n');
  const date = extractDates(source);

  const parsed = extractFirstLemma(afterImports);
  if (!parsed) {
    return {
      user,
      module,
      imports,
      open: openParts.length ? openParts : [],
      set_option: '[]',
      def: [],
      lemma: [],
      error: [
        {
          type: 'stub',
          info: 'Could not find a `lemma` declaration (stub parser).',
          code: '',
          line: 0,
        },
      ],
      date,
    };
  }

  return {
    user,
    module,
    imports,
    open: openParts.length ? openParts : [],
    set_option: '[]',
    def: [],
    lemma: [parsed],
    error: [],
    date,
  };
}

function extractDates(text) {
  const created = text.match(/--\s*created on\s+(\d{4}-\d{2}-\d{2})/i);
  const updated = text.match(/--\s*updated on\s+(\d{4}-\d{2}-\d{2})/i);
  return {
    created: created ? created[1] : new Date().toISOString().slice(0, 10),
    updated: updated ? updated[1] : null,
  };
}

function extractFirstLemma(text) {
  const commentM = text.match(/^\s*\/--([\s\S]*?)-\/\s*/m);
  const comment = commentM ? commentM[1].trim() : null;
  let body = commentM ? text.slice(commentM[0].length) : text;

  const attrM = body.match(/@\[([^\]]+)\]/);
  const attribute = attrM ? attrM[1].split(/\s*,\s*/) : null;

  const lemmaM = body.match(
    /\b(private|protected|public|noncomputable)?\s*lemma\s+(\w+)\b/m
  );
  if (!lemmaM) return null;
  const accessibility = lemmaM[1] || 'private';
  const name = lemmaM[2];

  const givenIdx = body.indexOf('-- given');
  const implyIdx = body.indexOf('-- imply');
  const proofIdx = body.indexOf('-- proof');

  let instImplicit = '';
  const headerEnd =
    givenIdx >= 0
      ? givenIdx
      : implyIdx >= 0
        ? implyIdx
        : proofIdx >= 0
          ? proofIdx
          : body.length;
  const header = body.slice(0, headerEnd);
  const headerLines = header.split('\n');
  const brackets = [];
  for (const line of headerLines) {
    const t = line.trim();
    if (t.startsWith('[') && t.endsWith(']')) brackets.push(t);
  }
  if (brackets.length) instImplicit = brackets.map((b) => `  ${b}`).join('\n');

  let explicit = '';
  let given = null;
  let defaultPart = '';
  if (givenIdx >= 0 && implyIdx > givenIdx) {
    const givenSection = body.slice(givenIdx + '-- given'.length, implyIdx).trim();
    explicit = givenSection;
  }

  let implyLean = '';
  let proofPart = '';
  if (implyIdx >= 0) {
    const afterImply = body.slice(implyIdx + '-- imply'.length);
    const pRel = afterImply.indexOf('-- proof');
    if (pRel >= 0) {
      implyLean = afterImply.slice(0, pRel).trim();
      /** Do not `.trim()` proof text — it strips leading indent on the first tactic line and breaks `splitProofIntoTacticBlocks`. */
      proofPart = afterImply.slice(pRel + '-- proof'.length).replace(/^\n+/, '');
    } else {
      implyLean = afterImply.trim();
    }
  }

  proofPart = proofPart.replace(/\n\s*--\s*(created|updated)[\s\S]*$/i, '').trimEnd();

  const proof = buildProofStub(proofPart);

  const imply =
    implyLean.trim().length > 0
      ? {
          insert: false,
          lean: implyLean,
          /** Match PHP `\\tag*{ := by}` on the last line of the `align` block. */
          latex: leanToFallbackLatex(implyLean, { tag: ' := by' }),
        }
      : { insert: true, lean: implyLean, latex: '' };

  return {
    comment: comment || null,
    attribute: attribute || null,
    accessibility,
    name,
    instImplicit,
    strictImplicit: '',
    implicit: '',
    explicit,
    given,
    default: defaultPart,
    imply,
    proof,
  };
}

/**
 * Split `-- proof` into tactic blocks:
 * - minimum indent among non-empty lines = "column" where a new tactic starts;
 * - lines more indented than that are continuations (multi-line `have`, `rw [`, etc.);
 * - blank lines flush the current block (same as Lean layout conventions).
 *
 * Then each block gets `leanToFallbackLatex` (+ auto `\tag*` from `denote` / `have` / …).
 */
function splitProofIntoTacticBlocks(proofText) {
  const lines = proofText.split('\n');
  const nonempty = lines.filter((l) => l.trim());
  if (nonempty.length === 0) return [];
  /** Use first line’s indent — `Math.min` breaks if any line is outdented (e.g. column 0). */
  const baseIndent = lineIndent(nonempty[0]);

  const blocks = [];
  let buf = [];

  function flush() {
    if (buf.length === 0) return;
    blocks.push(buf.join('\n'));
    buf = [];
  }

  for (const line of lines) {
    if (!line.trim()) {
      flush();
      continue;
    }
    const ind = lineIndent(line);
    if (buf.length === 0) {
      buf.push(line);
    } else if (ind > baseIndent) {
      buf.push(line);
    } else {
      flush();
      buf.push(line);
    }
  }
  flush();
  return blocks;
}

function buildProofStub(proofText) {
  if (!proofText.trim()) return null;
  const blocks = splitProofIntoTacticBlocks(proofText);
  const tactics = blocks.map((lean) => ({
    lean,
    latex: leanToFallbackLatex(lean),
  }));
  if (!tactics.length) return null;
  return { by: tactics };
}
