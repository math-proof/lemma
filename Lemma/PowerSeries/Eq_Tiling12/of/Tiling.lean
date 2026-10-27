import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[tiling_1_2_unique_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (T : Tiling (Rectangle 1 2)) :
-- imply
  T = tiling_1_2 := by
-- proof
  -- Prove equality by showing dominos are equal
  have hdom : T.dominos = tiling_1_2.dominos := by
    ext d
    constructor
    · intro hd
      have hsub : d.toShape ⊆ Rectangle 1 2 := by
        rw [← T.cover]
        exact Set.subset_biUnion_of_mem hd
      cases d with
      | horizontal i j =>
        simp only [Domino.toShape] at hsub
        have h1 : (i, j) ∈ Rectangle 1 2 := hsub (Set.mem_insert _ _)
        have h2 : (i + 1, j) ∈ Rectangle 1 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        simp only [Rectangle, Set.mem_ofPred_eq] at h1 h2
        omega
      | vertical i j =>
        simp only [Domino.toShape] at hsub
        have h1 : (i, j) ∈ Rectangle 1 2 := hsub (Set.mem_insert _ _)
        have h2 : (i, j + 1) ∈ Rectangle 1 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
        simp only [Rectangle, Set.mem_ofPred_eq] at h1 h2
        have hi : i = 1 := by omega
        have hj : j = 1 := by omega
        subst hi hj
        exact Set.mem_singleton_iff.mpr rfl
    · intro hd
      simp only [tiling_1_2, Set.mem_singleton_iff] at hd
      subst hd
      have h11 : (1, 1) ∈ Rectangle 1 2 := by
        simp only [Rectangle, Set.mem_ofPred_eq]
        omega
      rw [← T.cover] at h11
      simp only [Set.mem_iUnion, exists_prop] at h11
      obtain ⟨d, hd, h11d⟩ := h11
      have hsub : d.toShape ⊆ Rectangle 1 2 := by
        rw [← T.cover]
        exact Set.subset_biUnion_of_mem hd
      cases d with
      | horizontal i j =>
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h11d
        rcases h11d with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · subst hi hj
          have h21 : @Prod.mk ℤ ℤ 2 1 ∈ (Domino.horizontal 1 1).toShape := by simp [Domino.toShape]
          have h21' : @Prod.mk ℤ ℤ 2 1 ∈ Rectangle 1 2 := hsub h21
          simp only [Rectangle, Set.mem_ofPred_eq] at h21'
          omega
        · have hi' : i = 0 := by omega
          subst hi' hj
          have h01 : @Prod.mk ℤ ℤ 0 1 ∈ (Domino.horizontal 0 1).toShape := by simp [Domino.toShape]
          have h01' : @Prod.mk ℤ ℤ 0 1 ∈ Rectangle 1 2 := hsub h01
          simp only [Rectangle, Set.mem_ofPred_eq] at h01'
          omega
      | vertical i j =>
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h11d
        rcases h11d with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · subst hi hj
          exact hd
        · have hj' : j = 0 := by omega
          subst hi hj'
          have h10 : @Prod.mk ℤ ℤ 1 0 ∈ (Domino.vertical 1 0).toShape := by simp [Domino.toShape]
          have h10' : @Prod.mk ℤ ℤ 1 0 ∈ Rectangle 1 2 := hsub h10
          simp only [Rectangle, Set.mem_ofPred_eq] at h10'
          omega
  exact Tiling.ext T tiling_1_2 hdom


-- created on 2026-10-20
