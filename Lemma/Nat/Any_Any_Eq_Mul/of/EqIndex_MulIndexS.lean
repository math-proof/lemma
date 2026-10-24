import Mathlib
import sympy.Basic
open MulAction


private lemma stabilizer_mk_one_eq
  {G : Type*}
  [Group G]
  (H₁ H₂ : Subgroup G) :
  stabilizer H₂ ((1 : G) : G ⧸ H₁) = H₁.subgroupOf H₂ := by
  ext h
  have key : h • ((1 : G) : G ⧸ H₁) = (((h : G) * 1 : G) : G ⧸ H₁) := rfl
  rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf, key, mul_one, QuotientGroup.eq, mul_one,
    inv_mem_iff]

private lemma exists_eq_mul_of_index_inf_eq
  {G : Type*}
  [Group G]
  [Finite G] (H₁ H₂ : Subgroup G)
  (h : (H₁ ⊓ H₂).index = H₁.index * H₂.index) (g : G) :
  ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂ := by
  have hrel : H₁.relIndex H₂ = H₁.index := by
    have h1 : H₁.relIndex H₂ * H₂.index = (H₁ ⊓ H₂).index := by
      rw [← Subgroup.inf_relIndex_right, Subgroup.relIndex_mul_index inf_le_right]
    rw [h] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
  have hcard : (orbit H₂ ((1 : G) : G ⧸ H₁)).ncard = (Set.univ : Set (G ⧸ H₁)).ncard := by
    rwa [← index_stabilizer, stabilizer_mk_one_eq, Set.ncard_univ, ← Subgroup.index_eq_card]
  have huniv : orbit H₂ ((1 : G) : G ⧸ H₁) = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) hcard.ge Set.finite_univ
  have hmem : ((g⁻¹ : G) : G ⧸ H₁) ∈ orbit H₂ ((1 : G) : G ⧸ H₁) := huniv ▸ Set.mem_univ _
  obtain ⟨h₂, hh₂⟩ := mem_orbit_iff.mp hmem
  have key : h₂ • ((1 : G) : G ⧸ H₁) = (((h₂ : G) * 1 : G) : G ⧸ H₁) := rfl
  rw [key, mul_one, QuotientGroup.eq] at hh₂
  refine ⟨g * h₂, ?_, (h₂ : G)⁻¹, H₂.inv_mem h₂.2, by group⟩
  have := H₁.inv_mem hh₂
  rwa [mul_inv_rev, inv_inv, inv_inv] at this
/--
[Subgroup_exists_eq_mul_of_index_inf_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Subgroup_exists_eq_mul_of_index_inf_eq.lean)
-/
@[path]
private lemma main
  [Group G] [Finite G]
  {H₁ H₂ : Subgroup G}
  {g : G}
-- given
  (h : (H₁ ⊓ H₂).index = H₁.index * H₂.index) :
-- imply
  ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂ :=
-- proof
  exists_eq_mul_of_index_inf_eq H₁ H₂ h g


-- created on 2026-10-23
