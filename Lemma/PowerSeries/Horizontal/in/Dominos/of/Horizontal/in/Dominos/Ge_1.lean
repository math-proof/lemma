import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


private lemma domino_subset_rect (n : ℕ) (T : Tiling (Rectangle n 2)) (d : Domino) (hd : d ∈ T.dominos) :
    d.toShape ⊆ Rectangle n 2 := by
  intro x hx
  have : x ∈ ⋃ d ∈ T.dominos, d.toShape := by
    simp only [Set.mem_iUnion]
    exact ⟨d, hd, hx⟩
  rw [T.cover] at this
  exact this


private lemma cell_12_in_rect (n : ℕ) (hn : n ≥ 1) : (1, 2) ∈ Rectangle n 2 := by
  simp only [Rectangle, Set.mem_ofPred_eq]; omega


private lemma exists_domino_covering_12 (n : ℕ) (hn : n ≥ 1) (T : Tiling (Rectangle n 2)) :
    ∃ d ∈ T.dominos, (1, 2) ∈ d.toShape := by
  have h12 : (1, 2) ∈ Rectangle n 2 := cell_12_in_rect n hn
  rw [← T.cover] at h12
  simp only [Set.mem_iUnion] at h12
  obtain ⟨d, hd, hmem⟩ := h12
  exact ⟨d, hd, hmem⟩


private lemma domino_covering_12_valid (n : ℕ) (T : Tiling (Rectangle n 2))
    (d : Domino) (hd : d ∈ T.dominos) (h : (1, 2) ∈ d.toShape) :
    d = .vertical 1 1 ∨ d = .horizontal 1 2 := by
  cases d with
  | horizontal i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · right; simp only [Domino.horizontal.injEq]; omega
    · exfalso
      have hcover : ((0 : ℤ), (2 : ℤ)) ∈ (Domino.horizontal i j).toShape := by
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        left; omega
      have := domino_subset_rect n T (Domino.horizontal i j) hd hcover
      simp only [Rectangle, Set.mem_ofPred_eq] at this; omega
  | vertical i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · exfalso
      have hcover : ((1 : ℤ), (3 : ℤ)) ∈ (Domino.vertical i j).toShape := by
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        right; omega
      have := domino_subset_rect n T (Domino.vertical i j) hd hcover
      simp only [Rectangle, Set.mem_ofPred_eq] at this; omega
    · left; simp only [Domino.vertical.injEq]; omega


/--
[horizontal_12_if_horizontal_11_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (hn : n ≥ 1)
  (hh : Domino.horizontal 1 1 ∈ T.dominos) :
-- imply
  Domino.horizontal 1 2 ∈ T.dominos := by
-- proof
  obtain ⟨d, hd, hmem⟩ := exists_domino_covering_12 n hn T
  have hcases := domino_covering_12_valid n T d hd hmem
  rcases hcases with rfl | rfl
  · exfalso
    have hdisj := T.pairwise_disjoint hd hh
    have hne : Domino.vertical 1 1 ≠ Domino.horizontal 1 1 := by simp
    have : Disjoint (Domino.vertical 1 1).toShape (Domino.horizontal 1 1).toShape := hdisj hne
    have h11_vert : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 1 1).toShape := by simp [Domino.toShape]
    have h11_horiz : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := by simp [Domino.toShape]
    exact Set.disjoint_iff.mp this ⟨h11_vert, h11_horiz⟩
  · exact hd


-- created on 2026-10-20
