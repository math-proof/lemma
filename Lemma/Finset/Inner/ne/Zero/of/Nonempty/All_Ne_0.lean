import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.Reflection.GenericFunctional
open Set
open scoped InnerProductSpace


/--
[exists_inner_ne_zero_of_finite_nonzero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/GenericFunctional.lean)
-/
@[path]
lemma exists_inner_ne_zero_of_finite_nonzero
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {S : Finset E}
-- given
  (hS : ∀ γ ∈ S, γ ≠ 0)
  (_hne : S.Nonempty) :
-- imply
  ∃ v : E, ∀ γ ∈ S, ⟪v, γ⟫_ℝ ≠ 0 := by
-- proof
  let kerMap : E → Subspace ℝ E := fun γ => LinearMap.ker (innerSL ℝ γ).toLinearMap
  let T : Finset (Subspace ℝ E) := S.image kerMap
  have hT_no_top : ⊤ ∉ T := by
    simp only [T, Finset.mem_image]
    rintro ⟨γ, hγ_mem, hγ_eq⟩
    have hγ_ne : γ ≠ 0 := hS γ hγ_mem
    have hker_ne_top : kerMap γ ≠ ⊤ := by
      intro h_top
      rw [show kerMap γ = LinearMap.ker (innerSL ℝ γ).toLinearMap from rfl,
        LinearMap.ker_eq_top] at h_top
      have : innerSL ℝ γ = 0 := ContinuousLinearMap.coe_injective h_top
      have : ‖innerSL ℝ γ‖ = 0 := by rw [this]; simp
      rw [innerSL_apply_norm] at this
      exact hγ_ne (norm_eq_zero.mp this)
    exact hker_ne_top (hγ_eq ▸ rfl)
  have hT_ne_univ : ⋃ p ∈ T, (p : Set E) ≠ Set.univ :=
    Subspace.biUnion_ne_univ_of_top_notMem hT_no_top
  obtain ⟨v, hv⟩ : ∃ v : E, v ∉ ⋃ p ∈ T, (p : Set E) := by
    by_contra h
    push_neg at h
    exact hT_ne_univ (Set.eq_univ_of_forall h)
  refine ⟨v, fun γ hγ h_eq => ?_⟩
  apply hv
  rw [Set.mem_iUnion₂]
  exact ⟨kerMap γ, Finset.mem_image.mpr ⟨γ, hγ, rfl⟩,
    LinearMap.mem_ker.mpr (by simp [real_inner_comm v γ, h_eq])⟩


-- created on 2026-10-24
