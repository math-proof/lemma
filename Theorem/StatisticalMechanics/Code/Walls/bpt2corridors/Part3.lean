/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bpt2corridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bxpxpos.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Def.StatisticalMechanics.Code.Walls.bpt2corridors.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


theorem bpt2_a₁_mem_S₁ : bmf_a₁ ∈ bpt2_S₁ := by
  refine ⟨?_, ?_⟩ <;> simp [bmf_a₁]

theorem bpt2_x₁_mem_S₁ : bmf_b₁ ∈ bpt2_S₁ := by
  refine ⟨?_, ?_⟩ <;> simp [bmf_b₁]

theorem bpt2_a₂_mem_S₂ : bmf_a₂ ∈ bpt2_S₂ := by
  refine ⟨?_, ?_⟩ <;> simp [bmf_a₂]

theorem bpt2_x₂_mem_S₂ : bmf_b₂ ∈ bpt2_S₂ := by
  refine ⟨?_, ?_⟩ <;> simp [bmf_b₂]

theorem bpt2_a₃_mem_S₃ : bmf_a₃ ∈ bpt2_S₃ := by
  refine ⟨?_, ?_⟩ <;> simp [bmf_a₃]

theorem bpt2_x₃_mem_S₃ : bmf_b₃ ∈ bpt2_S₃ := by
  refine ⟨?_, ?_⟩ <;> simp [bmf_b₃]


theorem bpt2_R₁_subset_S₁ {v : Site 2} (h : v ∈ bmf_R₁) : v ∈ bpt2_S₁ :=
  ⟨h.1, by have := h.2; omega⟩

theorem bpt2_R₂_subset_S₂ {v : Site 2} (h : v ∈ bmf_R₂) : v ∈ bpt2_S₂ :=
  ⟨h.1, by have := h.2; omega⟩

theorem bpt2_R₃_subset_S₃ {v : Site 2} (h : v ∈ bmf_R₃) : v ∈ bpt2_S₃ :=
  ⟨h.1, by have := h.2; omega⟩

theorem bpt2_S₁_notMem_S₂ {v : Site 2} (h : v ∈ bpt2_S₁) : v ∉ bpt2_S₂ := by
  rintro ⟨h0, _⟩; have := h.2; rw [h0] at this; omega

theorem bpt2_S₁_notMem_S₃ {v : Site 2} (h : v ∈ bpt2_S₁) : v ∉ bpt2_S₃ := by
  rintro ⟨_, h0⟩; have := h.2; omega

theorem bpt2_S₂_notMem_S₁ {v : Site 2} (h : v ∈ bpt2_S₂) : v ∉ bpt2_S₁ := by
  rintro ⟨_, h1⟩; have := h.1; rw [h.1] at h1; omega

theorem bpt2_S₂_notMem_S₃ {v : Site 2} (h : v ∈ bpt2_S₂) : v ∉ bpt2_S₃ := by
  rintro ⟨h0, _⟩; have := h.2; rw [h0] at this; omega

theorem bpt2_S₃_notMem_S₁ {v : Site 2} (h : v ∈ bpt2_S₃) : v ∉ bpt2_S₁ := by
  rintro ⟨_, h1⟩; have := h.2; omega

theorem bpt2_S₃_notMem_S₂ {v : Site 2} (h : v ∈ bpt2_S₃) : v ∉ bpt2_S₂ := by
  rintro ⟨h0, _⟩; have := h.2; rw [h0] at this; omega

theorem bpt2_disjoint_S₁_S₂ : Disjoint bpt2_S₁ bpt2_S₂ :=
  Set.disjoint_left.mpr fun _ ha hb => bpt2_S₁_notMem_S₂ ha hb

theorem bpt2_disjoint_S₁_S₃ : Disjoint bpt2_S₁ bpt2_S₃ :=
  Set.disjoint_left.mpr fun _ ha hb => bpt2_S₁_notMem_S₃ ha hb

theorem bpt2_disjoint_S₂_S₃ : Disjoint bpt2_S₂ bpt2_S₃ :=
  Set.disjoint_left.mpr fun _ ha hb => bpt2_S₂_notMem_S₃ ha hb


theorem bpt2_a₂_notMem_S₁ : bmf_a₂ ∉ bpt2_S₁ := by
  rintro ⟨h0, h1⟩; simp [bmf_a₂] at h0 h1

theorem bpt2_b₂_notMem_S₁ : bmf_b₂ ∉ bpt2_S₁ := by
  rintro ⟨h0, h1⟩; simp [bmf_b₂] at h0 h1

theorem bpt2_a₃_notMem_S₁ : bmf_a₃ ∉ bpt2_S₁ := by
  rintro ⟨h0, h1⟩; simp [bmf_a₃] at h0 h1

theorem bpt2_b₃_notMem_S₁ : bmf_b₃ ∉ bpt2_S₁ := by
  rintro ⟨h0, h1⟩; simp [bmf_b₃] at h0 h1

theorem bpt2_a₁_notMem_S₂ : bmf_a₁ ∉ bpt2_S₂ := by
  rintro ⟨h0, h1⟩; simp [bmf_a₁] at h0 h1

theorem bpt2_b₁_notMem_S₂ : bmf_b₁ ∉ bpt2_S₂ := by
  rintro ⟨h0, h1⟩; simp [bmf_b₁] at h0 h1

theorem bpt2_a₃_notMem_S₂ : bmf_a₃ ∉ bpt2_S₂ := by
  rintro ⟨h0, h1⟩; simp [bmf_a₃] at h0 h1

theorem bpt2_b₃_notMem_S₂ : bmf_b₃ ∉ bpt2_S₂ := by
  rintro ⟨h0, h1⟩; simp [bmf_b₃] at h0 h1

theorem bpt2_a₁_notMem_S₃ : bmf_a₁ ∉ bpt2_S₃ := by
  rintro ⟨h0, h1⟩; simp [bmf_a₁] at h0 h1

theorem bpt2_b₁_notMem_S₃ : bmf_b₁ ∉ bpt2_S₃ := by
  rintro ⟨h0, h1⟩; simp [bmf_b₁] at h0 h1

theorem bpt2_a₂_notMem_S₃ : bmf_a₂ ∉ bpt2_S₃ := by
  rintro ⟨h0, h1⟩; simp [bmf_a₂] at h0 h1

theorem bpt2_b₂_notMem_S₃ : bmf_b₂ ∉ bpt2_S₃ := by
  rintro ⟨h0, h1⟩; simp [bmf_b₂] at h0 h1


theorem bpt2_I_respects_S₁ (u v : Site 2) (hmem : s(u, v) ∈ bmf_I) (hu : u ∈ bpt2_S₁) :
    v ∈ bpt2_S₁ := by
  simp only [bmf_I, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h <;> rcases Sym2.eq_iff.mp h with ⟨hu', hv'⟩ | ⟨hu', hv'⟩ <;>
    subst hu' <;> subst hv'
  · exact bpt2_x₁_mem_S₁
  · exact bpt2_a₁_mem_S₁
  · exact absurd hu bpt2_a₂_notMem_S₁
  · exact absurd hu bpt2_b₂_notMem_S₁
  · exact absurd hu bpt2_a₃_notMem_S₁
  · exact absurd hu bpt2_b₃_notMem_S₁

theorem bpt2_I_respects_S₂ (u v : Site 2) (hmem : s(u, v) ∈ bmf_I) (hu : u ∈ bpt2_S₂) :
    v ∈ bpt2_S₂ := by
  simp only [bmf_I, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h <;> rcases Sym2.eq_iff.mp h with ⟨hu', hv'⟩ | ⟨hu', hv'⟩ <;>
    subst hu' <;> subst hv'
  · exact absurd hu bpt2_a₁_notMem_S₂
  · exact absurd hu bpt2_b₁_notMem_S₂
  · exact bpt2_x₂_mem_S₂
  · exact bpt2_a₂_mem_S₂
  · exact absurd hu bpt2_a₃_notMem_S₂
  · exact absurd hu bpt2_b₃_notMem_S₂

theorem bpt2_I_respects_S₃ (u v : Site 2) (hmem : s(u, v) ∈ bmf_I) (hu : u ∈ bpt2_S₃) :
    v ∈ bpt2_S₃ := by
  simp only [bmf_I, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h <;> rcases Sym2.eq_iff.mp h with ⟨hu', hv'⟩ | ⟨hu', hv'⟩ <;>
    subst hu' <;> subst hv'
  · exact absurd hu bpt2_a₁_notMem_S₃
  · exact absurd hu bpt2_b₁_notMem_S₃
  · exact absurd hu bpt2_a₂_notMem_S₃
  · exact absurd hu bpt2_b₂_notMem_S₃
  · exact bpt2_x₃_mem_S₃
  · exact bpt2_a₃_mem_S₃


theorem bpt2_a₁_notMem_rays :
    bmf_a₁ ∉ bmf_R₁ ∧ bmf_a₁ ∉ bmf_R₂ ∧ bmf_a₁ ∉ bmf_R₃ := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h0, h1⟩; simp [bmf_a₁] at h0 h1
  · rintro ⟨h0, h1⟩; simp [bmf_a₁] at h0 h1
  · rintro ⟨h0, h1⟩; simp [bmf_a₁] at h0 h1

theorem bpt2_a₂_notMem_rays :
    bmf_a₂ ∉ bmf_R₁ ∧ bmf_a₂ ∉ bmf_R₂ ∧ bmf_a₂ ∉ bmf_R₃ := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h0, h1⟩; simp [bmf_a₂] at h0 h1
  · rintro ⟨h0, h1⟩; simp [bmf_a₂] at h0 h1
  · rintro ⟨h0, h1⟩; simp [bmf_a₂] at h0 h1

theorem bpt2_a₃_notMem_rays :
    bmf_a₃ ∉ bmf_R₁ ∧ bmf_a₃ ∉ bmf_R₂ ∧ bmf_a₃ ∉ bmf_R₃ := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h0, h1⟩; simp [bmf_a₃] at h0 h1
  · rintro ⟨h0, h1⟩; simp [bmf_a₃] at h0 h1
  · rintro ⟨h0, h1⟩; simp [bmf_a₃] at h0 h1


theorem bpt2_notOnRay_of_endpoint {e : Sym2 (Site 2)} {a : Site 2} (hae : a ∈ e)
    (hR : a ∉ bmf_R₁ ∧ a ∉ bmf_R₂ ∧ a ∉ bmf_R₃) : ¬ bmf_OnRay e := by
  rintro ⟨x, y, heq, hcases⟩
  subst heq
  rw [Sym2.mem_iff] at hae
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hae with rfl | rfl
  · exact hR.1 h1
  · exact hR.1 h2
  · exact hR.2.1 h1
  · exact hR.2.1 h2
  · exact hR.2.2 h1
  · exact hR.2.2 h2


theorem bpt2_closeI_omegaTri : bpt2_closeI bmf_I bmf_omegaTri = bmf_omegaTri := by
  funext e
  unfold bpt2_closeI
  by_cases h : e ∈ bmf_I
  · rw [if_pos h]
    symm
    rw [← Bool.not_eq_true, bmf_omegaTri_true]
    simp only [bmf_I, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl
    · exact bpt2_notOnRay_of_endpoint (by simp) bpt2_a₁_notMem_rays
    · exact bpt2_notOnRay_of_endpoint (by simp) bpt2_a₂_notMem_rays
    · exact bpt2_notOnRay_of_endpoint (by simp) bpt2_a₃_notMem_rays
  · rw [if_neg h]


theorem bpt2_S₁_closed (u v : Site 2) (hu : u ∈ bpt2_S₁)
    (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) u v) : v ∈ bpt2_S₁ := by
  have hop2 := hop.2
  have hraw : bmf_omegaTri s(u, v) = true := by
    by_cases h0 : (0 : Site 2) ∈ s(u, v)
    · rw [removeSite_apply_of_mem h0] at hop2; exact absurd hop2 (by simp)
    · rw [removeSite_apply_of_notMem h0] at hop2; exact hop2
  obtain ⟨x', y', heq, hcases⟩ := bmf_omegaTri_true.mp hraw
  rcases Sym2.eq_iff.mp heq with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  · subst hxx; subst hyy
    rcases hcases with ⟨_, hy'⟩ | ⟨hx', _⟩ | ⟨hx', _⟩
    · exact bpt2_R₁_subset_S₁ hy'
    · exact absurd (bpt2_R₂_subset_S₂ hx') (bpt2_S₁_notMem_S₂ hu)
    · exact absurd (bpt2_R₃_subset_S₃ hx') (bpt2_S₁_notMem_S₃ hu)
  · subst hxy; subst hyx
    rcases hcases with ⟨hy', _⟩ | ⟨_, hx'⟩ | ⟨_, hx'⟩
    · exact bpt2_R₁_subset_S₁ hy'
    · exact absurd (bpt2_R₂_subset_S₂ hx') (bpt2_S₁_notMem_S₂ hu)
    · exact absurd (bpt2_R₃_subset_S₃ hx') (bpt2_S₁_notMem_S₃ hu)

theorem bpt2_S₂_closed (u v : Site 2) (hu : u ∈ bpt2_S₂)
    (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) u v) : v ∈ bpt2_S₂ := by
  have hop2 := hop.2
  have hraw : bmf_omegaTri s(u, v) = true := by
    by_cases h0 : (0 : Site 2) ∈ s(u, v)
    · rw [removeSite_apply_of_mem h0] at hop2; exact absurd hop2 (by simp)
    · rw [removeSite_apply_of_notMem h0] at hop2; exact hop2
  obtain ⟨x', y', heq, hcases⟩ := bmf_omegaTri_true.mp hraw
  rcases Sym2.eq_iff.mp heq with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  · subst hxx; subst hyy
    rcases hcases with ⟨hx', _⟩ | ⟨_, hy'⟩ | ⟨hx', _⟩
    · exact absurd (bpt2_R₁_subset_S₁ hx') (bpt2_S₂_notMem_S₁ hu)
    · exact bpt2_R₂_subset_S₂ hy'
    · exact absurd (bpt2_R₃_subset_S₃ hx') (bpt2_S₂_notMem_S₃ hu)
  · subst hxy; subst hyx
    rcases hcases with ⟨_, hx'⟩ | ⟨hy', _⟩ | ⟨_, hx'⟩
    · exact absurd (bpt2_R₁_subset_S₁ hx') (bpt2_S₂_notMem_S₁ hu)
    · exact bpt2_R₂_subset_S₂ hy'
    · exact absurd (bpt2_R₃_subset_S₃ hx') (bpt2_S₂_notMem_S₃ hu)

theorem bpt2_S₃_closed (u v : Site 2) (hu : u ∈ bpt2_S₃)
    (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) u v) : v ∈ bpt2_S₃ := by
  have hop2 := hop.2
  have hraw : bmf_omegaTri s(u, v) = true := by
    by_cases h0 : (0 : Site 2) ∈ s(u, v)
    · rw [removeSite_apply_of_mem h0] at hop2; exact absurd hop2 (by simp)
    · rw [removeSite_apply_of_notMem h0] at hop2; exact hop2
  obtain ⟨x', y', heq, hcases⟩ := bmf_omegaTri_true.mp hraw
  rcases Sym2.eq_iff.mp heq with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  · subst hxx; subst hyy
    rcases hcases with ⟨hx', _⟩ | ⟨hx', _⟩ | ⟨_, hy'⟩
    · exact absurd (bpt2_R₁_subset_S₁ hx') (bpt2_S₃_notMem_S₁ hu)
    · exact absurd (bpt2_R₂_subset_S₂ hx') (bpt2_S₃_notMem_S₂ hu)
    · exact bpt2_R₃_subset_S₃ hy'
  · subst hxy; subst hyx
    rcases hcases with ⟨_, hx'⟩ | ⟨_, hx'⟩ | ⟨hy', _⟩
    · exact absurd (bpt2_R₁_subset_S₁ hx') (bpt2_S₃_notMem_S₁ hu)
    · exact absurd (bpt2_R₂_subset_S₂ hx') (bpt2_S₃_notMem_S₂ hu)
    · exact bpt2_R₃_subset_S₃ hy'


end StatMech.Walls
