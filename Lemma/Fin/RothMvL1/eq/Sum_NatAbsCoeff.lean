import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvL1_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ) :
-- imply
  rothMvL1 P = ∑ i ∈ P.support, (P.coeff i).natAbs := by
-- proof
  unfold rothMvL1 rothFinsuppL1
  rw [← MvPolynomial.finsupp_support_eq_support]


-- created on 2026-10-21
