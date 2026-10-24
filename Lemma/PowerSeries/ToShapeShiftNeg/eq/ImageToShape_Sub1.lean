import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[domino_shift_neg_to_shape_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (d : Domino)
  (offset : ℕ) :
-- imply
  (d.shiftNeg offset).toShape = d.toShape.image (fun p => (p.1 - (offset : ℤ), p.2)) := by
-- proof
  simp only [shiftNeg, shift_toShape]
  ext ⟨x, y⟩
  simp only [Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨x', y'⟩, hp, hx, hy⟩
    exact ⟨⟨x', y'⟩, hp, by omega, hy⟩
  · rintro ⟨⟨x', y'⟩, hp, hx, hy⟩
    exact ⟨⟨x', y'⟩, hp, by omega, hy⟩


-- created on 2026-10-20
