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


/--
[domino_covering_11_valid_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (d : Domino)
  (hd : d ∈ T.dominos)
  (h : (1, 1) ∈ d.toShape) :
-- imply
  d = .vertical 1 1 ∨ d = .horizontal 1 1 := by
-- proof
  cases d with
  | horizontal i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · right; simp only [Domino.horizontal.injEq]; omega
    · exfalso
      have hcover : ((0 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal i j).toShape := by
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        left; omega
      have := domino_subset_rect n T (Domino.horizontal i j) hd hcover
      simp only [Rectangle, Set.mem_ofPred_eq] at this; omega
  | vertical i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · left; simp only [Domino.vertical.injEq]; omega
    · exfalso
      have hcover : ((1 : ℤ), (0 : ℤ)) ∈ (Domino.vertical i j).toShape := by
        simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
        left; omega
      have := domino_subset_rect n T (Domino.vertical i j) hd hcover
      simp only [Rectangle, Set.mem_ofPred_eq] at this; omega


-- created on 2026-10-20
