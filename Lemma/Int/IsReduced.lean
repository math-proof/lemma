import Mathlib
import sympy.Basic

open IsLocalRing TensorProduct

/--
[IsLocalRing_isReduced_residueField_tensorProduct_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_isReduced_residueField_tensorProduct_iff.lean)
-/
@[main]
private lemma main
  [CommRing A] [IsLocalRing A] [CommRing R] [Algebra A R] :
-- imply
  IsReduced (ResidueField A ⊗[A] R) ↔ IsReduced (R ⧸ (maximalIdeal A).map (algebraMap A R)) := by
-- proof
  let e : ResidueField A ⊗[A] R ≃ₐ[A] R ⧸ (maximalIdeal A).map (algebraMap A R) :=
    (Algebra.TensorProduct.comm A (ResidueField A) R).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (maximalIdeal A)).symm.restrictScalars A)
  exact ⟨fun _ => isReduced_of_injective e.symm e.symm.injective,
    fun _ => isReduced_of_injective e e.injective⟩


-- created on 2026-10-03
