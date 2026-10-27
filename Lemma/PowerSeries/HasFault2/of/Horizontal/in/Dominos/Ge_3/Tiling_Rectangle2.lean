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


private lemma no_horizontal_at_2_if_horizontal_pair (n : ℕ) (T : Tiling (Rectangle n 2))
    (hh1 : Domino.horizontal 1 1 ∈ T.dominos) (hh2 : Domino.horizontal 1 2 ∈ T.dominos)
    (i j : ℤ) (hd : Domino.horizontal i j ∈ T.dominos) : i < 2 ∨ i ≥ 3 := by
  by_contra h; push Not at h; obtain ⟨hi1, hi2⟩ := h
  have hi : i = 2 := by omega
  have hsub := domino_subset_rect n T (Domino.horizontal i j) hd
  have hij : ((i : ℤ), j) ∈ Rectangle n 2 := hsub (by simp [Domino.toShape])
  simp only [Rectangle, Set.mem_ofPred_eq] at hij
  have hj12 : j = 1 ∨ j = 2 := by omega
  rcases hj12 with rfl | rfl
  · have hdisj := T.pairwise_disjoint hh1 hd
    have hne : Domino.horizontal 1 1 ≠ Domino.horizontal i 1 := by simp; omega
    have : Disjoint (Domino.horizontal 1 1).toShape (Domino.horizontal i 1).toShape := hdisj hne
    have h21_h11 : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := by simp [Domino.toShape]
    have h21_hi1 : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal i 1).toShape := by simp [Domino.toShape, hi]
    exact Set.disjoint_iff.mp this ⟨h21_h11, h21_hi1⟩
  · have hdisj := T.pairwise_disjoint hh2 hd
    have hne : Domino.horizontal 1 2 ≠ Domino.horizontal i 2 := by simp; omega
    have : Disjoint (Domino.horizontal 1 2).toShape (Domino.horizontal i 2).toShape := hdisj hne
    have h22_h12 : ((2 : ℤ), (2 : ℤ)) ∈ (Domino.horizontal 1 2).toShape := by simp [Domino.toShape]
    have h22_hi2 : ((2 : ℤ), (2 : ℤ)) ∈ (Domino.horizontal i 2).toShape := by simp [Domino.toShape, hi]
    exact Set.disjoint_iff.mp this ⟨h22_h12, h22_hi2⟩


/--
[fault_at_2_if_horizontal_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (hn : n ≥ 3)
  (hh : Domino.horizontal 1 1 ∈ T.dominos) :
-- imply
  hasFault n T 2 := by
-- proof
  have hn1 : n ≥ 1 := by omega
  have hh2 := horizontal_12_if_horizontal_11 n hn1 T hh
  refine ⟨by omega, by omega, ?_⟩
  intro d hd
  cases d with
  | horizontal i j =>
    have := no_horizontal_at_2_if_horizontal_pair n T hh hh2 i j hd
    rcases this with h | h
    · left; omega
    · right; omega
  | vertical i j => trivial


-- created on 2026-10-20
