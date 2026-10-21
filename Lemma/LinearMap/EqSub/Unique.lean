import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[LinearMap_existsUnique_sub_eq_comp_comp_of_extension](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_existsUnique_sub_eq_comp_comp_of_extension.lean)
-/
@[path]
private lemma main
    {R : Type u} [CommRing R]
    {K : Type v} {M : Type w} {M' : Type w'} {E : Type x}
    [AddCommGroup K] [Module R K] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup E] [Module R E]
    (ϑ : K →ₗ[R] M) (θ : M →ₗ[R] E) (ϑ' : K →ₗ[R] M') (θ' : M' →ₗ[R] E)
    (hθ : Function.Surjective θ) (hex : LinearMap.range ϑ = LinearMap.ker θ)
    (hϑ' : Function.Injective ϑ') (hex' : LinearMap.range ϑ' = LinearMap.ker θ')
    (α β : M →ₗ[R] M') (hK : α ∘ₗ ϑ = β ∘ₗ ϑ) (hE : θ' ∘ₗ α = θ' ∘ₗ β) :
    ∃! γ : E →ₗ[R] K, α - β = ϑ' ∘ₗ γ ∘ₗ θ := by
  classical
  set δ : M →ₗ[R] M' := α - β with hδ
  have hδK : ∀ m : M, θ m = 0 → δ m = 0 := by
    intro m hm
    have : m ∈ LinearMap.range ϑ := by rw [hex]; exact hm
    obtain ⟨k, rfl⟩ := this
    have := congrArg (fun f : K →ₗ[R] M' => f k) hK
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    simp [hδ, this]
  have hδE : ∀ m : M, δ m ∈ LinearMap.range ϑ' := by
    intro m
    rw [hex', LinearMap.mem_ker]
    have := congrArg (fun f : M →ₗ[R] E => f m) hE
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    simp [hδ, this]
  obtain ⟨δ', hδ'⟩ : ∃ δ' : E →ₗ[R] M', δ' ∘ₗ θ = δ := by
    refine ⟨(LinearMap.ker θ).liftQ δ (fun m hm => hδK m hm) ∘ₗ
      (LinearMap.quotKerEquivOfSurjective θ hθ).symm.toLinearMap, ?_⟩
    ext m
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    have : (LinearMap.quotKerEquivOfSurjective θ hθ).symm (θ m) = Submodule.Quotient.mk m := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    rw [this, Submodule.liftQ_apply]
  have hδ'E : ∀ e : E, δ' e ∈ LinearMap.range ϑ' := by
    intro e
    obtain ⟨m, rfl⟩ := hθ e
    have : δ' (θ m) = δ m := congrArg (fun f : M →ₗ[R] M' => f m) hδ'
    rw [this]
    exact hδE m
  let ι : E →ₗ[R] LinearMap.range ϑ' := LinearMap.codRestrict _ δ' hδ'E
  let e' : K ≃ₗ[R] LinearMap.range ϑ' := LinearEquiv.ofInjective ϑ' hϑ'
  refine ⟨e'.symm.toLinearMap ∘ₗ ι, ?_, ?_⟩
  · ext m
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    have h1 : ϑ' (e'.symm (ι (θ m))) = (ι (θ m)).1 := by
      have := LinearEquiv.ofInjective_apply ϑ' (h := hϑ') (e'.symm (ι (θ m)))
      rw [LinearEquiv.apply_symm_apply] at this
      exact this.symm
    rw [h1]
    change δ m = δ' (θ m)
    exact (congrArg (fun f : M →ₗ[R] M' => f m) hδ').symm
  · intro γ hγ
    ext e
    obtain ⟨m, rfl⟩ := hθ e
    apply hϑ'
    have h1 : ϑ' (γ (θ m)) = δ m := by
      have := congrArg (fun f : M →ₗ[R] M' => f m) hγ
      simp only [LinearMap.coe_comp, Function.comp_apply] at this
      exact this.symm
    have h2 : ϑ' ((e'.symm.toLinearMap ∘ₗ ι) (θ m)) = δ m := by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
      have := LinearEquiv.ofInjective_apply ϑ' (h := hϑ') (e'.symm (ι (θ m)))
      rw [LinearEquiv.apply_symm_apply] at this
      rw [← this]
      change δ' (θ m) = δ m
      exact congrArg (fun f : M →ₗ[R] M' => f m) hδ'
    rw [h1, h2]

-- created on 2026-10-20
