import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvL1_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} :
-- imply
  rothMvL1 (1 : MvPolynomial (Fin m) ℤ) = 1 := by
-- proof
  classical
  have hmono (i : RothMvIndex m) (c : ℤ) :
    rothMvL1 (MvPolynomial.monomial i c) = c.natAbs := by
    change rothFinsuppL1 (Finsupp.single i c) = c.natAbs
    if hc : c = 0 then
      simp [hc, rothFinsuppL1]
    else
      simp [rothFinsuppL1, hc]
  rw [show (1 : MvPolynomial (Fin m) ℤ) = MvPolynomial.monomial 0 1 by simp]
  rw [hmono]
  norm_num


-- created on 2026-10-21
