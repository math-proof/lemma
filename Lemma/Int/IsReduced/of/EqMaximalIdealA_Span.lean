import Mathlib
import sympy.Basic

open IsLocalRing TensorProduct

/--
[IsLocalRing_isReduced_residueField_tensorProduct_iff_of_maximalIdeal_eq_span](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_isReduced_residueField_tensorProduct_iff_of_maximalIdeal_eq_span.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsLocalRing A] [CommRing R] [Algebra A R]
  {a : A}
-- given
  (ha : maximalIdeal A = Ideal.span {a}) :
-- imply
  IsReduced (ResidueField A ⊗[A] R) ↔ IsReduced (R ⧸ Ideal.span {algebraMap A R a}) := by
-- proof
  have hI : (maximalIdeal A).map (algebraMap A R) = Ideal.span {algebraMap A R a} := by
    rw [ha, Ideal.map_span, Set.image_singleton]
  let e : ResidueField A ⊗[A] R ≃+* R ⧸ Ideal.span {algebraMap A R a} :=
    ((Algebra.TensorProduct.comm A (ResidueField A) R).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R (maximalIdeal A)).symm.restrictScalars A)).toRingEquiv.trans (Ideal.quotEquivOfEq hI)
  exact ⟨fun _ => isReduced_of_injective e.symm e.symm.injective,
    fun _ => isReduced_of_injective e e.injective⟩


-- created on 2026-10-05
