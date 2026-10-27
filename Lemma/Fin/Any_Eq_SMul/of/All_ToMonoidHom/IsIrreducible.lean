import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.LieGroups.code.SchurLemma
open scoped ComplexOrder


/--
[schur_scalar_finiteDim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SchurLemma.lean)
-/
@[path]
lemma schur_scalar_finiteDim
  [Group G]
  [AddCommGroup V]
  [Module ℂ V]
  [FiniteDimensional ℂ V]
  [Nontrivial V]
  {π : FinDimRep G V}
  {T : V →ₗ[ℂ] V}
-- given
  (hirr : π.IsIrreducible)
  (hT : ∀ g : G, T ∘ₗ π.toMonoidHom g = π.toMonoidHom g ∘ₗ T) :
-- imply
  ∃ c : ℂ, T = c • LinearMap.id := by
-- proof
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  set S : Module.End ℂ V := T - μ • 1 with hS_def
  have hS_intertwines : ∀ g : G, S ∘ₗ π.toMonoidHom g = π.toMonoidHom g ∘ₗ S := by
    intro g
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, hS_def]
    have h1 : (1 : Module.End ℂ V) (π.toMonoidHom g v) = π.toMonoidHom g v := rfl
    have h2 : (1 : Module.End ℂ V) v = v := rfl
    rw [h1, h2, map_sub, map_smul]
    congr 1
    exact LinearMap.ext_iff.mp (hT g) v
  have hker_inv : ∀ g : G, ∀ v ∈ LinearMap.ker S,
    π.toMonoidHom g v ∈ LinearMap.ker S := by
    intro g v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have := LinearMap.ext_iff.mp (hS_intertwines g) v
    simp only [LinearMap.comp_apply] at this
    rwa [hv, map_zero] at this
  have hker_ne_bot : LinearMap.ker S ≠ ⊥ := by
    rw [hS_def, ← Module.End.eigenspace_def]
    exact Module.End.hasEigenvalue_iff.mp hμ
  have hker_top : LinearMap.ker S = ⊤ := by
    cases hirr (LinearMap.ker S) hker_inv with
    | inl h => exact absurd h hker_ne_bot
    | inr h => exact h
  have hS_zero : S = 0 := LinearMap.ker_eq_top.mp hker_top
  exact ⟨μ, by have := sub_eq_zero.mp hS_zero; rw [this]; rfl⟩


-- created on 2026-10-23
