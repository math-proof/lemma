# arXiv paper rules

Shared rules for every folder under `website/arxiv/<paper>/`.
There is no per-paper `SUBMIT.md`. Title, Chinese filename, and lemma.cn links live in that folder’s `main.tex` and Zhihu `*.md`.

## Files

| File | Role |
|------|------|
| `main.tex` | arXiv source. This is the paper. |
| `refs.bib` | BibTeX database. Cited only from `main.tex`. |
| `main.bbl` | Pre-generated bibliography. **Required in the upload zip.** arXiv does not run BibTeX. |
| `main.pdf` | Local preview only. Do **not** upload. Do **not** link readers to the repo PDF. |
| `<Chinese title>.md` | Zhihu writeup. Not part of the arXiv zip. |

Do not use `main.md` for the Chinese file.

**Sync:** edit `main.tex` → rebuild `main.pdf` (and `main.bbl` if citations changed) → update the Zhihu `*.md` to match. After arXiv acceptance, put the arXiv URL in the Zhihu file (参考文献), not a link to `main.pdf`.

## `main.tex`

- One paper, one `main.tex`, compiled with pdfLaTeX.
- Bibliography: classic BibTeX (`\bibliographystyle{…}` + `\bibliography{refs}`), not `biblatex`/`biber`.
- Lemma names as clickable text via `\href{http://www.lemma.cn/lean/?module=…}{…}` or `\lmod{…}`. Do not print the raw `http://…` string next to the name.
- Keep the upload **flat**: no subdirectories. Extra figures, if any, sit next to `main.tex`.

## `main.bbl` and `main.pdf`

Requires TeX Live or MiKTeX. From the paper folder:

```bash
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

The argument to `bibtex` is `main` (it reads `main.aux`), not `refs`.

| Pass | Writes |
|------|--------|
| first `pdflatex` | `main.aux` (citation keys) |
| `bibtex main` | `main.bbl` from `refs.bib` |
| second `pdflatex` | inserts the bibliography |
| third `pdflatex` | settles citation numbers, cross-references, bookmarks |

If you only change wording and not `\cite` keys or `refs.bib`, two `pdflatex` passes are enough. After a bibliography change, keep all four steps.

Check the end of `main.log` for `Error` or unresolved `?` citations before upload.

## Upload zip

Flat zip, three files only (plus optional PNGs if `\includegraphics` is used):

- `main.tex`
- `refs.bib`
- `main.bbl`

Choose **pdfLaTeX**. Do not include `main.pdf`, `*.md`, or this `submit.md`.
Submit before 14:00 US Eastern (Mon–Fri) for same-day announcement.

First-time `cs.*` submitters need endorsement in the **primary** category. That is per category, not per paper.

**Comments** (every paper): Lean 4 formalization; code at https://github.com/math-proof/lemma

## Categories

Every paper is a Lean 4 formalization, so `cs.LO` is always on the list. Primary is the subject, not the proof assistant.

| Subject | Primary | Secondary |
|---------|---------|-----------|
| Machine learning or RL (attention, transformers, KV-cache, RoPE, policies, …) | `cs.LG` | `cs.LO`, and `cs.CL` / `cs.AI` when the object is language models or agents |
| Pure mathematics (equations, analysis, algebra, …) | `cs.LO` | matching `math.*` (e.g. `math.CV`), and `cs.SC` when the object is symbolic computation |

Do not list `cs.PL` unless the paper is about a programming language, not merely written in Lean.

Ask for endorsement in the primary only (`cs.LG` for ML/RL, `cs.LO` for pure math). Do not mix codes across papers.

## Zhihu `*.md`

Audience: Zhihu readers (知乎读者). This file is not the arXiv source.

- **Filename:** Chinese translation of the arXiv title, plus `.md`. Do not use `main.md`.
- **Headings:** only `#` and `##` (no `###` or deeper).
- **Author line:** omit the arXiv author name (Zhihu anonymity). A project-artifact link is enough.
- **Hyperlink** `[text](url)`: both sides must be free of markdown special tokens. No LaTeX (`\(`, `$`, `\mathrm`, …), no backtick code spans, and no ASCII apostrophe `'`. A parser can take `'` as the start of a link title, so `[共轭](…RotaryMatrix'.eq…)` is broken. Put math or `code` outside the brackets. The lemma name **is** the `module=` query and the Linux path; do not replace `'` with a lookalike (Unicode prime `′` is a different character and will 404). Write the path apostrophe as `%27` in the URL, and in the label whenever the label is the lemma name: `[RotaryMatrix%27.eq.DotDot_RotaryMatrix](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix%27.eq.DotDot_RotaryMatrix)`. A Chinese word as label is fine: `[共轭](http://www.lemma.cn/lean/?module=Tensor.RotaryMatrix%27.eq.DotDot_RotaryMatrix)`.
- Lemma names are markdown links to lemma.cn, not raw `http://…` in the body.
- Do not link to repo `main.pdf`. Add the arXiv URL after acceptance.
- Keep section-for-section correspondence with `main.tex` (chapters, formulas, figure numbers, bibliography).
