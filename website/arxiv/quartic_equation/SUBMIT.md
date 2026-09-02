# arXiv submission bundle: principal-radical quartic over C

## Contents

| File | Purpose |
|------|---------|
| `main.tex` | Paper source (arXiv) |
| `复数域一元四次方程完全根式解.md` | Chinese Markdown (Zhihu); filename = Chinese title |
| `main.pdf` | Compiled paper |
| `refs.bib` | Bibliography database |
| `main.bbl` | Pre-generated bibliography (arXiv does not run BibTeX) |

**Sync rule:** Edit `main.tex` → rebuild `main.pdf`. The `*.md` file is the Chinese (Zhihu) writeup. Do not link readers to repo `main.pdf`; add the arXiv URL in the `*.md` file after acceptance.

## Chinese Markdown rules

- Audience: Zhihu readers (知乎读者). This file is not the arXiv source.
- Headings: use only `#` and `##` (no `###` or deeper).
- Filename: the Chinese translation of the arXiv title, plus `.md`. Here that is `复数域一元四次方程完全根式解.md` for *Fully Radical Solution of the Quartic Equation over \(\mathbb{C}\)*. Do not use `main.md`.

## Build locally

Requires a TeX distribution (TeX Live or MiKTeX).

```bash
cd website/arxiv/quartic_equation
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
    - **Primary category:** `cs.LO`
    - **Secondary:** `cs.SC`, optional `math.CV`
    - **Comments:** Lean 4 formalization; code at https://github.com/math-proof/lemma
7. Submit before 14:00 US Eastern (Mon–Fri) for same-day announcement.

## Optional figures

The paper uses in-line LaTeX diagrams (no external image files required).
To add lemma.cn screenshots later:

1. Export PNG from SymPy and Lean pages.
2. Add `\includegraphics{fig0_sympy.png}`.
3. Include PNG files in the upload zip.
