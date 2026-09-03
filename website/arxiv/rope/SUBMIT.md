# arXiv submission bundle: 1D RoPE formalization

## Contents

| File | Purpose |
|------|---------|
| `main.tex` | Paper source (arXiv) |
| `refs.bib` | Bibliography database |
| `main.bbl` | Pre-generated bibliography (arXiv does not run BibTeX; produce this locally before upload) |

## Build locally

Requires a TeX distribution (TeX Live or MiKTeX).

```bash
cd website/arxiv/rope
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
4. Choose **pdfLaTeX** (default TeX Live).
5. Verify the compiled PDF preview.
6. Suggested metadata:
   - **Primary category:** `cs.LO` or `cs.LG`
   - **Secondary:** `cs.CL`, `cs.AI`
   - **Title:** Lean 4-Checked Identities for One-Dimensional Rotary Position Embeddings
   - **Comments:** Lean 4 formalization; code at https://github.com/math-proof/lemma
7. Submit before 14:00 US Eastern (Mon–Fri) for same-day announcement.

## Interactive lemmas (lemma.cn)

- Relative softmax: http://www.lemma.cn/lean/?module=Tensor.DotSoftmaxDivDot_Stack_TDot.eq.Stack_Div_SumExp.of.Eq_Stack_Mul
- RoFormer pairing: http://www.lemma.cn/lean/?module=Tensor.DotDotSRotaryMatrix.eq.Dot_DotRotaryMatrixSub
- Realization: http://www.lemma.cn/lean/?module=Tensor.DotRotaryMatrix.eq.AddMulS
- Additive: http://www.lemma.cn/lean/?module=Tensor.DotRotaryMatrixS.eq.RotaryMatrixAdd
- Orthogonal: http://www.lemma.cn/lean/?module=Tensor.DotT_RotaryMatrix.eq.Eye

## First-time cs.* submitters

You may need endorsement from an existing arXiv author in `cs.LO` or `cs.LG`.
