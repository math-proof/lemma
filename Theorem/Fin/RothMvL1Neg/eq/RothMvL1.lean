module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvL1_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothMvL1Neg.eq.RothMvL1
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ) :
-- imply
  rothMvL1 (-P) = rothMvL1 P := by
-- proof
  classical
  unfold rothMvL1 rothFinsuppL1
  rw [show (-P).coeff = -P.coeff from rfl, Finsupp.support_neg]
  congr with a
  exact Int.natAbs_neg _


-- updated on 2026-11-13
-- created on 2026-10-21
