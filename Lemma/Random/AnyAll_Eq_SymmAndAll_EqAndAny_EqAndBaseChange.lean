import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[LinearEquiv_exists_equiv_forall_dual_eq_comp_symm_and_comp_eq_of_dual_equiv_forall_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearEquiv_exists_equiv_forall_dual_eq_comp_symm_and_comp_eq_of_dual_equiv_forall_comp_eq.lean)
-/
@[path]
private lemma main
  (R : Type*) [CommRing R] (k : Type*) [CommRing k] [Algebra R k]
    (Ω : Type*) [AddCommGroup Ω] [Module R Ω] [Module.Finite R Ω] [Module.Free R Ω]
    (S : Type*) [AddCommGroup S] [Module R S] [Module.Finite R S] [Module.Free R S]
    (a : ι → (Ω →ₗ[R] Ω)) (s : ι → (S →ₗ[R] S))
    (τ : Module.Dual R Ω ≃ₗ[R] Module.Dual R S)
    (hτ : ∀ (t : ι) (D : Module.Dual R Ω), τ (LinearMap.comp D (a t)) = LinearMap.comp (τ D) (s t)) :
    -- imply
    ∃ θ : Ω ≃ₗ[R] S,
      (∀ D : Module.Dual R Ω, τ D = LinearMap.comp D (θ.symm : S →ₗ[R] Ω)) ∧
      (∀ t : ι, LinearMap.comp (θ : Ω →ₗ[R] S) (a t) = LinearMap.comp (s t) (θ : Ω →ₗ[R] S)) ∧
      ∃ Ξ : k ⊗[R] Ω ≃ₗ[k] k ⊗[R] S,
        (∀ (c : k) (x : Ω), Ξ (c ⊗ₜ x) = c ⊗ₜ θ x) ∧
        ∀ t : ι, LinearMap.comp (Ξ : k ⊗[R] Ω →ₗ[k] k ⊗[R] S) ((a t).baseChange k) =
          LinearMap.comp ((s t).baseChange k) (Ξ : k ⊗[R] Ω →ₗ[k] k ⊗[R] S) := by
    -- proof
  classical
  let ψ : S ≃ₗ[R] Ω :=
    (Module.evalEquiv R S).trans (τ.dualMap.trans (Module.evalEquiv R Ω).symm)
  have hψ : ∀ (D : Module.Dual R Ω) (y : S), D (ψ y) = τ D y := by
    intro D y
    simp [ψ, Module.apply_evalEquiv_symm_apply, LinearEquiv.dualMap_apply, Module.Dual.eval_apply]
  have key : ∀ (t : ι) (y : S), a t (ψ y) = ψ (s t y) := by
    intro t y
    apply (Module.evalEquiv R Ω).injective
    ext D
    simp only [Module.evalEquiv_apply, Module.Dual.eval_apply]
    calc
      _ = (LinearMap.comp D (a t)) (ψ y) := rfl
      _ = τ (LinearMap.comp D (a t)) y := hψ _ _
      _ = (LinearMap.comp (τ D) (s t)) y := by rw [hτ]
      _ = τ D (s t y) := rfl
      _ = D (ψ (s t y)) := (hψ _ _).symm
  have hcomp : ∀ t : ι, LinearMap.comp (ψ.symm : Ω →ₗ[R] S) (a t) = LinearMap.comp (s t) (ψ.symm : Ω →ₗ[R] S) := by
    intro t
    ext x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    obtain ⟨y, rfl⟩ : ∃ y, ψ y = x := ⟨ψ.symm x, by simp⟩
    rw [key t y]
    simp
  refine ⟨ψ.symm, ?_, hcomp, ?_⟩
  ·
    intro D
    ext y
    simp [hψ]
  ·
    refine ⟨ψ.symm.baseChange R k Ω S, ?_, ?_⟩
    ·
      intro c x
      simp [LinearEquiv.baseChange_tmul]
    ·
      intro t
      rw [LinearEquiv.coe_baseChange, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hcomp t]


-- created on 2026-10-20
