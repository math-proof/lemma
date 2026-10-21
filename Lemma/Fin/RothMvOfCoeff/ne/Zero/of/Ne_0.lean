import Mathlib
import Lemma.Fin.EqCoeffRothMvOfCoeffRothBoxIndex.of.RothBox.RothCoeff
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvOfCoeff_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} {r : Fin m → ℕ} {c : RothCoeff r}
-- given
  (hc : c ≠ 0) :
-- imply
  rothMvOfCoeff c ≠ 0 := by
-- proof
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
  intro hzero
  have := congrArg (fun P : MvPolynomial (Fin m) ℤ ↦ P.coeff (rothBoxIndex j)) hzero
  rw [EqCoeffRothMvOfCoeffRothBoxIndex.of.RothBox.RothCoeff, AddMonoidAlgebra.coeff_zero] at this
  exact hj this


-- created on 2026-10-21
