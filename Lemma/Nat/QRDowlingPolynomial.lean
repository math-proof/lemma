import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.QRDowlingPolynomial
open scoped BigOperators
open MetaMathlibExt


/--
[qrDowlingNumber_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QRDowlingPolynomial.lean)
-/
@[path]
private lemma qrDowlingNumber_eq_sum_eq
  [Semiring R]
  {W : ℕ → ℕ → R}
  {n : ℕ} :
-- imply
  qrDowlingNumber W n = ∑ k ∈ Finset.range (n + 1), W n k := by
-- proof
  apply MetaMathlibExt.qrDowlingNumber_eq_sum W n


-- created on 2026-10-20
