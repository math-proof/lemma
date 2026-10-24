import Mathlib

open scoped TensorProduct
open AdicCompletion

/-! FLT IsAdicComplete of Module.Finite over IsNoetherianRing (shared; not a rendered path). -/

universe u

namespace AdicCompletionSupport

theorem isAdicComplete_of_finite_aux {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsAdicComplete I M := by
  rw [← AdicCompletion.of_bijective_iff]
  let e1 : M ≃ₗ[R] R ⊗[R] M := (TensorProduct.lid R M).symm
  let e2 : R ⊗[R] M ≃ₗ[R] AdicCompletion I R ⊗[R] M :=
    LinearEquiv.rTensor M (AdicCompletion.ofLinearEquiv I R)
  let e3 : AdicCompletion I R ⊗[R] M ≃ₗ[R] AdicCompletion I M :=
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R
  have : (of I M : M → _) = e3 ∘ e2 ∘ e1 := by
    funext x
    simp only [e1, e2, e3, Function.comp_apply, LinearEquiv.restrictScalars_apply,
      ofTensorProductEquivOfFiniteNoetherian_apply, TensorProduct.lid_symm_apply,
      LinearEquiv.rTensor_tmul, ofLinearEquiv_apply, ofTensorProduct_tmul]
    have h1 : (of I R) 1 = 1 := by
      have := (AdicCompletion.algebraMap_apply (S := R) (I := I) (1 : R)).symm
      rw [map_one] at this
      simpa using this
    rw [h1, one_smul]
  rw [this]; exact e3.bijective.comp (e2.bijective.comp e1.bijective)

theorem isAdicComplete_of_linearEquiv {R : Type*} [CommRing R] (I : Ideal R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) [IsAdicComplete I M] : IsAdicComplete I N := by
  rw [← AdicCompletion.of_bijective_iff]
  have h : (of I N : N → _) = (AdicCompletion.congr I e) ∘ (of I M) ∘ e.symm := by
    funext x
    simp [AdicCompletion.congr_apply, map_of]
  rw [h]
  exact (AdicCompletion.congr I e).bijective.comp
    ((AdicCompletion.of_bijective I M).comp e.symm.bijective)

theorem isAdicComplete_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsAdicComplete I M := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  have : IsAdicComplete I ((Fin n → R) ⧸ LinearMap.ker p) := isAdicComplete_of_finite_aux I _
  exact isAdicComplete_of_linearEquiv I (p.quotKerEquivOfSurjective hp)

theorem isAdicComplete_of_moduleFinite_of_isNoetherianRing
    {R : Type*} [CommRing R] [IsNoetherianRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {I : Ideal R} [IsAdicComplete I R] :
    IsAdicComplete I M :=
  isAdicComplete_of_finite I M

end AdicCompletionSupport
