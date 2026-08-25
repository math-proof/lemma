# arXiv submission bundle: KV-cache formal verification

## Contents

| File | Purpose |
|------|---------|
| `main.tex` | Paper source (arXiv) |
| `main.md` | 中文 Markdown 版，与 `main.pdf` **一一对应**（章节、公式、图号、参考文献）；引理依赖树含可点击链接 |
| `main.pdf` | Compiled paper |
| `refs.bib` | Bibliography database |
| `main.bbl` | Pre-generated bibliography (arXiv does not run BibTeX) |

**Sync rule:** Edit `main.tex` → rebuild `main.pdf` → mirror the same structure in `main.md` (Chinese, section-for-section). Do not link readers to repo `main.pdf`; add arXiv URL in `main.md` §参考文献 after acceptance.

## Build locally

Requires a TeX distribution (TeX Live or MiKTeX).

```bash
cd website/arxiv/kv_cache
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

Output: `main.pdf`

## Upload to arXiv

1. Register at https://arxiv.org/user/register if needed.
2. **Start New Submission** from your user page.
3. Upload a **flat zip** containing:
   - `main.tex`
   - `refs.bib`
   - `main.bbl`
4. Choose **pdfLaTeX** (default TeX Live 2025).
5. Verify the compiled PDF preview.
6. Suggested metadata:
   - **Primary category:** `cs.LG` or `cs.PL`
   - **Secondary:** `cs.CL`, `cs.AI`
   - **Comments:** Lean 4 formalization; code at https://github.com/math-proof/lemma
7. Submit before 14:00 US Eastern (Mon–Fri) for same-day announcement.

## Optional figures

The paper uses in-line LaTeX diagrams (no external image files required).
To add lemma.cn screenshots later:

1. Export PNG from SymPy and Lean pages.
2. Add `\usepackage{graphicx}` and `\includegraphics{fig0_sympy.png}`.
3. Include PNG files in the upload zip.

## First-time cs.* submitters

You may need endorsement from an existing arXiv author in `cs.LG` or `cs.PL`.
