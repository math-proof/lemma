import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvL1_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
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


-- created on 2026-10-21
