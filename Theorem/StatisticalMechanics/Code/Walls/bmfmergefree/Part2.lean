/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bdecdecouple
import Def.StatisticalMechanics.Code.Walls.bmfmergefree.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


theorem bmf_omegaTri_true {e : Sym2 (Site 2)} : bmf_omegaTri e = true ↔ bmf_OnRay e := by
  unfold bmf_omegaTri; by_cases h : bmf_OnRay e <;> simp [h]


theorem bmf_R₁_notMem_R₂ {x : Site 2} (h : x ∈ bmf_R₁) : x ∉ bmf_R₂ := by
  rintro ⟨hx0, _⟩; exact absurd (hx0 ▸ h.2) (by norm_num)

theorem bmf_R₁_notMem_R₃ {x : Site 2} (h : x ∈ bmf_R₁) : x ∉ bmf_R₃ := by
  rintro ⟨_, hx0⟩; exact absurd (le_trans h.2 hx0) (by norm_num)

theorem bmf_R₂_notMem_R₁ {x : Site 2} (h : x ∈ bmf_R₂) : x ∉ bmf_R₁ :=
  fun h' => bmf_R₁_notMem_R₂ h' h

theorem bmf_R₂_notMem_R₃ {x : Site 2} (h : x ∈ bmf_R₂) : x ∉ bmf_R₃ := by
  rintro ⟨hx1, _⟩; exact absurd (hx1 ▸ h.2) (by norm_num)

theorem bmf_R₃_notMem_R₁ {x : Site 2} (h : x ∈ bmf_R₃) : x ∉ bmf_R₁ :=
  fun h' => bmf_R₁_notMem_R₃ h' h

theorem bmf_R₃_notMem_R₂ {x : Site 2} (h : x ∈ bmf_R₃) : x ∉ bmf_R₂ :=
  fun h' => bmf_R₂_notMem_R₃ h' h


theorem bmf_walk_invariant {ω : ConfigSpace (Sym2 (Site 2))} {S : Set (Site 2)}
    (hclosed : ∀ x y : Site 2, x ∈ S → IsOpenEdge 2 ω x y → y ∈ S)
    {x y : Site 2} (w : (openSubgraph 2 ω).Walk x y) (hx : x ∈ S) : y ∈ S := by
  induction w with
  | nil => exact hx
  | @cons a b c hab _ ih => exact ih (hclosed a b hx hab)


theorem bmf_cluster_subset {ω : ConfigSpace (Sym2 (Site 2))} {S : Set (Site 2)} {b : Site 2}
    (hb : b ∈ S) (hclosed : ∀ x y : Site 2, x ∈ S → IsOpenEdge 2 ω x y → y ∈ S) :
    cluster 2 ω b ⊆ S := by
  intro y hy
  obtain ⟨w⟩ := (hy : (openSubgraph 2 ω).Reachable b y)
  exact bmf_walk_invariant hclosed w hb


theorem bmf_R₁_closed (x y : Site 2) (hx : x ∈ bmf_R₁)
    (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) x y) : y ∈ bmf_R₁ := by
  have hop2 := hop.2
  have hraw : bmf_omegaTri s(x, y) = true := by
    by_cases h0 : (0 : Site 2) ∈ s(x, y)
    · rw [removeSite_apply_of_mem h0] at hop2; exact absurd hop2 (by simp)
    · rw [removeSite_apply_of_notMem h0] at hop2; exact hop2
  obtain ⟨x', y', heq, hcases⟩ := bmf_omegaTri_true.mp hraw
  rcases Sym2.eq_iff.mp heq with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  · subst hxx; subst hyy
    rcases hcases with ⟨_, hy'⟩ | ⟨hx', _⟩ | ⟨hx', _⟩
    · exact hy'
    · exact absurd hx' (bmf_R₁_notMem_R₂ hx)
    · exact absurd hx' (bmf_R₁_notMem_R₃ hx)
  · subst hxy; subst hyx
    rcases hcases with ⟨hy', _⟩ | ⟨_, hx'⟩ | ⟨_, hx'⟩
    · exact hy'
    · exact absurd hx' (bmf_R₁_notMem_R₂ hx)
    · exact absurd hx' (bmf_R₁_notMem_R₃ hx)

theorem bmf_R₂_closed (x y : Site 2) (hx : x ∈ bmf_R₂)
    (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) x y) : y ∈ bmf_R₂ := by
  have hop2 := hop.2
  have hraw : bmf_omegaTri s(x, y) = true := by
    by_cases h0 : (0 : Site 2) ∈ s(x, y)
    · rw [removeSite_apply_of_mem h0] at hop2; exact absurd hop2 (by simp)
    · rw [removeSite_apply_of_notMem h0] at hop2; exact hop2
  obtain ⟨x', y', heq, hcases⟩ := bmf_omegaTri_true.mp hraw
  rcases Sym2.eq_iff.mp heq with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  · subst hxx; subst hyy
    rcases hcases with ⟨hx', _⟩ | ⟨_, hy'⟩ | ⟨hx', _⟩
    · exact absurd hx' (bmf_R₂_notMem_R₁ hx)
    · exact hy'
    · exact absurd hx' (bmf_R₂_notMem_R₃ hx)
  · subst hxy; subst hyx
    rcases hcases with ⟨_, hx'⟩ | ⟨hy', _⟩ | ⟨_, hx'⟩
    · exact absurd hx' (bmf_R₂_notMem_R₁ hx)
    · exact hy'
    · exact absurd hx' (bmf_R₂_notMem_R₃ hx)

theorem bmf_R₃_closed (x y : Site 2) (hx : x ∈ bmf_R₃)
    (hop : IsOpenEdge 2 (removeSite 0 bmf_omegaTri) x y) : y ∈ bmf_R₃ := by
  have hop2 := hop.2
  have hraw : bmf_omegaTri s(x, y) = true := by
    by_cases h0 : (0 : Site 2) ∈ s(x, y)
    · rw [removeSite_apply_of_mem h0] at hop2; exact absurd hop2 (by simp)
    · rw [removeSite_apply_of_notMem h0] at hop2; exact hop2
  obtain ⟨x', y', heq, hcases⟩ := bmf_omegaTri_true.mp hraw
  rcases Sym2.eq_iff.mp heq with ⟨hxx, hyy⟩ | ⟨hxy, hyx⟩
  · subst hxx; subst hyy
    rcases hcases with ⟨hx', _⟩ | ⟨hx', _⟩ | ⟨_, hy'⟩
    · exact absurd hx' (bmf_R₃_notMem_R₁ hx)
    · exact absurd hx' (bmf_R₃_notMem_R₂ hx)
    · exact hy'
  · subst hxy; subst hyx
    rcases hcases with ⟨_, hx'⟩ | ⟨_, hx'⟩ | ⟨hy', _⟩
    · exact absurd hx' (bmf_R₃_notMem_R₁ hx)
    · exact absurd hx' (bmf_R₃_notMem_R₂ hx)
    · exact hy'


theorem bmf_b₁_mem_R₁ : bmf_b₁ ∈ bmf_R₁ := ⟨by simp [bmf_b₁], by simp [bmf_b₁]⟩

theorem bmf_b₂_mem_R₂ : bmf_b₂ ∈ bmf_R₂ := ⟨by simp [bmf_b₂], by simp [bmf_b₂]⟩

theorem bmf_b₃_mem_R₃ : bmf_b₃ ∈ bmf_R₃ := ⟨by simp [bmf_b₃], by simp [bmf_b₃]⟩


theorem bmf_b₁_conn_ray (k : ℕ) :
    Connected 2 (removeSite 0 bmf_omegaTri) bmf_b₁ ![2 + (k : ℤ), 0] := by
  induction k with
  | zero => simp only [Nat.cast_zero, add_zero, bmf_b₁]; exact connected_refl _ _
  | succ n ih =>
    rw [Nat.cast_succ]
    have hA : (![2 + (n : ℤ), 0] : Site 2) ∈ bmf_R₁ :=
      ⟨by simp, by simp only [Matrix.cons_val_zero]; omega⟩
    have hB : (![2 + ((n : ℤ) + 1), 0] : Site 2) ∈ bmf_R₁ :=
      ⟨by simp, by simp only [Matrix.cons_val_zero]; omega⟩
    have hadj : (hypercubicLattice 2).Adj (![2 + (n : ℤ), 0]) (![2 + ((n : ℤ) + 1), 0]) := by
      simp only [hypercubicLattice_adj, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]; omega
    have h0 : (0 : Site 2) ∉ s((![2 + (n : ℤ), 0] : Site 2), (![2 + ((n : ℤ) + 1), 0] : Site 2)) := by
      rw [Sym2.mem_iff]; push_neg
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
        · have := congrFun h 0; simp only [Pi.zero_apply, Matrix.cons_val_zero] at this; omega
    exact ih.trans (IsOpenEdge.connected ⟨hadj, by
      rw [removeSite_apply_of_notMem h0, bmf_omegaTri_true]; exact ⟨_, _, rfl, Or.inl ⟨hA, hB⟩⟩⟩)

theorem bmf_b₁_cluster_infinite :
    (cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₁).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (![2 + (k : ℤ), 0] : Site 2))
    ?_ ?_
  · intro a b hab
    have h := congrFun hab 0
    simp only [Matrix.cons_val_zero] at h
    exact_mod_cast (by omega : (a : ℤ) = (b : ℤ))
  · intro k; exact mem_cluster.mpr (bmf_b₁_conn_ray k)


theorem bmf_b₂_conn_ray (k : ℕ) :
    Connected 2 (removeSite 0 bmf_omegaTri) bmf_b₂ ![0, 2 + (k : ℤ)] := by
  induction k with
  | zero => simp only [Nat.cast_zero, add_zero, bmf_b₂]; exact connected_refl _ _
  | succ n ih =>
    rw [Nat.cast_succ]
    have hA : (![0, 2 + (n : ℤ)] : Site 2) ∈ bmf_R₂ :=
      ⟨by simp, by simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]; omega⟩
    have hB : (![0, 2 + ((n : ℤ) + 1)] : Site 2) ∈ bmf_R₂ :=
      ⟨by simp, by simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]; omega⟩
    have hadj : (hypercubicLattice 2).Adj (![0, 2 + (n : ℤ)]) (![0, 2 + ((n : ℤ) + 1)]) := by
      simp only [hypercubicLattice_adj, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]; omega
    have h0 : (0 : Site 2) ∉ s((![0, 2 + (n : ℤ)] : Site 2), (![0, 2 + ((n : ℤ) + 1)] : Site 2)) := by
      rw [Sym2.mem_iff]; push_neg
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
        · have := congrFun h 1
          simp only [Pi.zero_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at this; omega
    exact ih.trans (IsOpenEdge.connected ⟨hadj, by
      rw [removeSite_apply_of_notMem h0, bmf_omegaTri_true]
      exact ⟨_, _, rfl, Or.inr (Or.inl ⟨hA, hB⟩)⟩⟩)

theorem bmf_b₂_cluster_infinite :
    (cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₂).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (![0, 2 + (k : ℤ)] : Site 2))
    ?_ ?_
  · intro a b hab
    have h := congrFun hab 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at h
    exact_mod_cast (by omega : (a : ℤ) = (b : ℤ))
  · intro k; exact mem_cluster.mpr (bmf_b₂_conn_ray k)


theorem bmf_b₃_conn_ray (k : ℕ) :
    Connected 2 (removeSite 0 bmf_omegaTri) bmf_b₃ ![-2 - (k : ℤ), 0] := by
  induction k with
  | zero => simp only [Nat.cast_zero, sub_zero, bmf_b₃]; exact connected_refl _ _
  | succ n ih =>
    rw [Nat.cast_succ]
    have hA : (![-2 - (n : ℤ), 0] : Site 2) ∈ bmf_R₃ :=
      ⟨by simp, by simp only [Matrix.cons_val_zero]; omega⟩
    have hB : (![-2 - ((n : ℤ) + 1), 0] : Site 2) ∈ bmf_R₃ :=
      ⟨by simp, by simp only [Matrix.cons_val_zero]; omega⟩
    have hadj : (hypercubicLattice 2).Adj (![-2 - (n : ℤ), 0]) (![-2 - ((n : ℤ) + 1), 0]) := by
      simp only [hypercubicLattice_adj, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons]; omega
    have h0 : (0 : Site 2) ∉ s((![-2 - (n : ℤ), 0] : Site 2), (![-2 - ((n : ℤ) + 1), 0] : Site 2)) := by
      rw [Sym2.mem_iff]; push_neg
      refine ⟨fun h => ?_, fun h => ?_⟩ <;>
        · have := congrFun h 0; simp only [Pi.zero_apply, Matrix.cons_val_zero] at this; omega
    exact ih.trans (IsOpenEdge.connected ⟨hadj, by
      rw [removeSite_apply_of_notMem h0, bmf_omegaTri_true]
      exact ⟨_, _, rfl, Or.inr (Or.inr ⟨hA, hB⟩)⟩⟩)

theorem bmf_b₃_cluster_infinite :
    (cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₃).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (![-2 - (k : ℤ), 0] : Site 2))
    ?_ ?_
  · intro a b hab
    have h := congrFun hab 0
    simp only [Matrix.cons_val_zero] at h
    exact_mod_cast (by omega : (a : ℤ) = (b : ℤ))
  · intro k; exact mem_cluster.mpr (bmf_b₃_conn_ray k)


theorem bmf_omegaTri_mem_X : bmf_omegaTri ∈ bmf_X := by
  have hc1 : cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₁ ⊆ bmf_R₁ :=
    bmf_cluster_subset bmf_b₁_mem_R₁ bmf_R₁_closed
  have hc2 : cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₂ ⊆ bmf_R₂ :=
    bmf_cluster_subset bmf_b₂_mem_R₂ bmf_R₂_closed
  have hc3 : cluster 2 (removeSite 0 bmf_omegaTri) bmf_b₃ ⊆ bmf_R₃ :=
    bmf_cluster_subset bmf_b₃_mem_R₃ bmf_R₃_closed
  refine ⟨⟨bmf_b₁_cluster_infinite, bmf_b₂_cluster_infinite, bmf_b₃_cluster_infinite⟩,
    ?_, ?_, ?_⟩
  · intro h; exact bmf_R₁_notMem_R₂ (hc1 (mem_cluster.mpr h)) bmf_b₂_mem_R₂
  · intro h; exact bmf_R₁_notMem_R₃ (hc1 (mem_cluster.mpr h)) bmf_b₃_mem_R₃
  · intro h; exact bmf_R₂_notMem_R₃ (hc2 (mem_cluster.mpr h)) bmf_b₃_mem_R₃


theorem bmf_X_nonempty : bmf_X.Nonempty := ⟨bmf_omegaTri, bmf_omegaTri_mem_X⟩

end StatMech.Walls
