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
[horizontal_12_not_in_shift_nat2_image_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (m : ℕ)
  (T : Tiling (Rectangle m 2)) :
-- imply
  Domino.horizontal 1 2 ∉ T.dominos.image (fun d => d.shiftNat 2) := by
-- proof
  simp only [Set.mem_image, not_exists, not_and]
  intro d hd heq
  cases d with
  | horizontal i j =>
    simp only [Domino.shiftNat, Domino.shift, Domino.horizontal.injEq] at heq
    have hsub := domino_subset_rect m T (Domino.horizontal i j) hd
    have hi_ge : i ≥ 1 := by
      have := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq] at this
      exact this.1
    omega
  | vertical i j =>
    simp only [Domino.shiftNat, Domino.shift] at heq
    exact Domino.noConfusion heq


-- created on 2026-10-20
