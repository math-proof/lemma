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


/--
[vertical_11_not_in_shift_nat_image_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (m : ℕ)
  (T : Tiling (Rectangle m 2)) :
-- imply
  Domino.vertical 1 1 ∉ T.dominos.image (fun d => d.shiftNat 1) := by
-- proof
  simp only [Set.mem_image, not_exists, not_and]
  intro d hd heq
  cases d with
  | horizontal i j =>
    simp only [Domino.shiftNat, Domino.shift] at heq
    exact Domino.noConfusion heq
  | vertical i j =>
    simp only [Domino.shiftNat, Domino.shift, Domino.vertical.injEq] at heq
    have hsub := domino_subset_rect m T (Domino.vertical i j) hd
    have hi_ge : i ≥ 1 := by
      have := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq] at this
      exact this.1
    omega


-- created on 2026-10-20
