module

public import Mathlib
public import Theorem.Fin.EqCoeffRothMvOfCoeffRothBoxIndex.of.RothBox.RothCoeff

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvOfCoeff_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothMvOfCoeff.ne.Zero.of.Ne_0
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
