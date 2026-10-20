import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
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


private lemma no_horizontal_at_1_if_vertical (n : ℕ) (T : Tiling (Rectangle n 2))
    (hv : Domino.vertical 1 1 ∈ T.dominos) (i j : ℤ)
    (hd : Domino.horizontal i j ∈ T.dominos) : i < 1 ∨ i ≥ 2 := by
  have hdisj := T.pairwise_disjoint hv hd
  by_contra h; push Not at h; obtain ⟨hi1, hi2⟩ := h
  have hi : i = 1 := by omega
  have hd' : Domino.horizontal 1 j ∈ T.dominos := by rwa [hi] at hd
  have hsub := domino_subset_rect n T (Domino.horizontal 1 j) hd'
  have h1j : ((1 : ℤ), j) ∈ Rectangle n 2 := hsub (by simp [Domino.toShape])
  simp only [Rectangle, Set.mem_ofPred_eq] at h1j
  have hj12 : j = 1 ∨ j = 2 := by omega
  have h_in_horiz : ((1 : ℤ), j) ∈ (Domino.horizontal 1 j).toShape := by simp [Domino.toShape]
  have h_in_vert : ((1 : ℤ), j) ∈ (Domino.vertical 1 1).toShape := by
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    rcases hj12 with rfl | rfl <;> simp
  have hne : Domino.vertical 1 1 ≠ Domino.horizontal i j := by simp
  have hdisj' : Disjoint (Domino.vertical 1 1).toShape (Domino.horizontal i j).toShape := hdisj hne
  rw [hi] at hdisj'
  exact Set.disjoint_iff.mp hdisj' ⟨h_in_vert, h_in_horiz⟩


/--
[fault_at_1_if_vertical_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (hn : n ≥ 2)
  (hv : Domino.vertical 1 1 ∈ T.dominos) :
-- imply
  hasFault n T 1 := by
-- proof
  refine ⟨by omega, by omega, ?_⟩
  intro d hd
  cases d with
  | horizontal i j =>
    have := no_horizontal_at_1_if_vertical n T hv i j hd
    rcases this with h | h
    · left; omega
    · right; omega
  | vertical i j => trivial


-- created on 2026-10-20
