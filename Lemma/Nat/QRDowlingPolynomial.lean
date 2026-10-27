import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.QRDowlingPolynomial
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[qrDowlingNumber_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QRDowlingPolynomial.lean)
-/
@[path]
lemma qrDowlingNumber_eq_sum
  [Semiring R]
  {W : ℕ → ℕ → R}
  {n : ℕ} :
-- imply
  qrDowlingNumber W n = ∑ k ∈ Finset.range (n + 1), W n k := by
-- proof
  rw [qrDowlingNumber, qrDowlingPolynomial, Polynomial.eval_finsetSum]
  simp

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
