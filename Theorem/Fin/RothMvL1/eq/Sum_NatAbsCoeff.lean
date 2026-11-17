module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvL1_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothMvL1.eq.Sum_NatAbsCoeff
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ) :
-- imply
  rothMvL1 P = ∑ i ∈ P.support, (P.coeff i).natAbs := by
-- proof
  unfold rothMvL1 rothFinsuppL1
  rw [← MvPolynomial.finsupp_support_eq_support]


-- updated on 2026-11-13
-- created on 2026-10-21
