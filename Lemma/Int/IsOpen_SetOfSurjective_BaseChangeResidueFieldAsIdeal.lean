import Mathlib
import sympy.Basic

open TensorProduct

/--
[LinearMap_isOpen_setOf_surjective_baseChange_residueField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_isOpen_setOf_surjective_baseChange_residueField.lean)
-/
@[main]
private lemma main
  {A : Type u} [CommRing A]
  {P : Type v} [AddCommGroup P] [Module A P]
  {Q : Type w} [AddCommGroup Q] [Module A Q]
  {d : P →ₗ[A] Q} [Module.Finite A (Q ⧸ LinearMap.range d)] :
-- imply
  IsOpen {𝔭 : PrimeSpectrum A | Function.Surjective (d.baseChange 𝔭.asIdeal.ResidueField)} := by
-- proof
  have key : ∀ (K : Type u) [CommRing K] [Algebra A K],
      Function.Surjective (d.baseChange K) ↔ Subsingleton (K ⊗[A] (Q ⧸ LinearMap.range d)) := by
    intro K _ _
    rw [(TensorProduct.tensorQuotientEquiv K (LinearMap.range d)).toEquiv.subsingleton_congr,
      Submodule.Quotient.subsingleton_iff, LinearMap.baseChange_eq_ltensor, ← LinearMap.range_eq_top]
    have : (TensorProduct.map LinearMap.id (LinearMap.range d).subtype).range = (LinearMap.lTensor K d).range :=
      (LinearMap.lTensor_range K).symm
    rw [this]

  have h : {𝔭 : PrimeSpectrum A | Function.Surjective (d.baseChange 𝔭.asIdeal.ResidueField)} =
      (Module.support A (Q ⧸ LinearMap.range d))ᶜ := by
    ext 𝔭
    rw [Set.mem_ofPred_eq, key, Set.mem_compl_iff, Module.mem_support_iff_nontrivial_residueField_tensorProduct,
      not_nontrivial_iff_subsingleton]
  rw [h]
  exact Module.isClosed_support.isOpen_compl


-- created on 2026-10-05
