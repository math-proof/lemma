import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma helper_main {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : Function.Bijective (f.baseChange K)) (R₂ : Type u) [CommRing R₂] [IsDomain R₂] [Algebra R R₂] (hinj : Function.Injective (algebraMap R R₂)) (K₂ : Type u) [Field K₂] [Algebra R₂ K₂] [IsFractionRing R₂ K₂] : Function.Bijective ((f.baseChange R₂).baseChange K₂) := by
  let algRK₂ : Algebra R K₂ := ((algebraMap R₂ K₂).comp (algebraMap R R₂)).toAlgebra
  let _ : IsScalarTower R R₂ K₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hinj₂ : Function.Injective (algebraMap R K₂) := (IsFractionRing.injective R₂ K₂).comp hinj
  have hunits : ∀ y : nonZeroDivisors R, IsUnit (algebraMap R K₂ y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr fun h => ?_
    apply nonZeroDivisors.ne_zero y.2 (hinj₂ (by rw [h, map_zero]))
  let ι : K →+* K₂ := IsLocalization.lift (M := nonZeroDivisors R) hunits
  let algKK₂ : Algebra K K₂ := ι.toAlgebra
  let _ : IsScalarTower R K K₂ := IsScalarTower.of_algebraMap_eq (fun r => by
    show algebraMap R K₂ r = ι (algebraMap R K r)
    rw [IsLocalization.lift_eq])
  let EM : K₂ ⊗[R₂] (R₂ ⊗[R] M) ≃ₗ[K₂] K₂ ⊗[K] (K ⊗[R] M) := (TensorProduct.AlgebraTensorModule.cancelBaseChange R R₂ K₂ K₂ M).trans (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K₂ K₂ M).symm
  let EN : K₂ ⊗[R₂] (R₂ ⊗[R] N) ≃ₗ[K₂] K₂ ⊗[K] (K ⊗[R] N) := (TensorProduct.AlgebraTensorModule.cancelBaseChange R R₂ K₂ K₂ N).trans (TensorProduct.AlgebraTensorModule.cancelBaseChange R K K₂ K₂ N).symm
  let e : K₂ ⊗[R₂] (R₂ ⊗[R] M) ≃ₗ[K₂] K₂ ⊗[R₂] (R₂ ⊗[R] N) := EM.trans ((LinearEquiv.baseChange K K₂ (K ⊗[R] M) (K ⊗[R] N) (LinearEquiv.ofBijective (f.baseChange K) hf)).trans EN.symm)
  have hsq : ∀ z, (f.baseChange R₂).baseChange K₂ z = e z := by
    intro z
    induction z using TensorProduct.inductionOn
    ·
      rename_i k w
      induction w using TensorProduct.inductionOn
      ·
        rename_i r m
        simp only [e, EM, EN, LinearEquiv.trans_apply, LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.baseChange_tmul, LinearEquiv.ofBijective_apply, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm]
        rw [one_smul, TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      ·
        rename_i x y hx hy
        simp only [TensorProduct.tmul_add, map_add, hx, hy]
    ·
      rename_i x y hx hy
      simp only [map_add, hx, hy]
  have hfun : ⇑((f.baseChange R₂).baseChange K₂) = ⇑e := funext hsq
  rw [hfun]
  apply e.bijective
/--
[LinearMap_bijective_baseChange_baseChange_of_bijective_baseChange_fractionRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_bijective_baseChange_baseChange_of_bijective_baseChange_fractionRing.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N)
  (hf : Function.Bijective (f.baseChange K))
  (R₂ : Type u) [CommRing R₂] [IsDomain R₂] [Algebra R R₂]
  (hinj : Function.Injective (algebraMap R R₂))
  (K₂ : Type u) [Field K₂] [Algebra R₂ K₂] [IsFractionRing R₂ K₂] :
  -- imply
  Function.Bijective ((f.baseChange R₂).baseChange K₂) := helper_main K f hf R₂ hinj K₂


-- created on 2026-10-20
