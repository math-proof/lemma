/**
 * Server-rendered reading view for a lemma page.
 * Formulas are KaTeX HTML in the first response. The editor stays on `?edit=1`.
 */
import katex from "katex";

function esc(value) {
  return String(value ?? "").replace(/[&<>"']/g, (ch) => ({
    "&": "&amp;",
    "<": "&lt;",
    ">": "&gt;",
    '"': "&quot;",
    "'": "&#39;",
  }[ch]));
}

function sanitizeLatex(latex) {
  return String(latex)
    .replace(/‡/g, "\\ddagger")
    .replace(/[†✝]/gi, "\\dagger");
}

function latexSource(latex) {
  if (latex == null || latex === "") return "";
  if (Array.isArray(latex)) return latex.filter(Boolean).join(" \\\\\n");
  if (typeof latex === "string") return latex;
  return "";
}

function formula(latex) {
  const source = latexSource(latex);
  if (!source) return "";
  let html;
  try {
    html = katex.renderToString(sanitizeLatex(source), {
      displayMode: true,
      throwOnError: false,
      errorColor: "#ff0000",
    });
  } catch {
    return `<pre class="reading-lean">${esc(source)}</pre>`;
  }
  return `<div class="reading-formula">${html}</div>`;
}

function proofSteps(proof) {
  if (!proof) return [];
  if (Array.isArray(proof)) return proof;
  if (Array.isArray(proof.by)) return proof.by;
  if (Array.isArray(proof.calc)) return proof.calc;
  return [];
}

function section(title, body) {
  if (!body) return "";
  return `<section class="reading-section"><h2>${esc(title)}</h2>${body}</section>`;
}

/**
 * @param {object} code lemma payload (`render2vue` / MySQL row)
 * @param {string} module dotted module name
 * @returns {string} HTML fragment
 */
export function renderReadingHtml(code, module) {
  const lemmas = Array.isArray(code?.lemma) ? code.lemma : [];
  const blocks = lemmas.map((lemma) => {
    const givens = (Array.isArray(lemma.given) ? lemma.given : [])
      .map((item) => formula(item?.latex) || (item?.lean ? `<pre class="reading-lean">${esc(item.lean)}</pre>` : ""))
      .join("");
    const imply = formula(lemma.imply?.latex)
      || (lemma.imply?.lean ? `<pre class="reading-lean">${esc(lemma.imply.lean)}</pre>` : "");
    const steps = proofSteps(lemma.proof).map((step) => {
      return formula(step?.latex) || (step?.lean ? `<pre class="reading-lean">${esc(step.lean)}</pre>` : "");
    }).join("");
    const name = lemma.name ? `<h2 class="reading-name">${esc(lemma.name)}</h2>` : "";
    return `<article class="reading-lemma">${name
    }${section("given", givens)}${section("imply", imply)}${section("proof", steps)}</article>`;
  }).join("");
  const title = module ? `<h1>${esc(module)}</h1>` : "";
  return `${title}${blocks}`;
}
