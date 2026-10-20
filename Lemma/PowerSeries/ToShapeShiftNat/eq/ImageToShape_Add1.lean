import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[domino_shift_nat_to_shape_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (d : Domino)
  (offset : ℕ) :
-- imply
  (d.shiftNat offset).toShape = d.toShape.image (fun p => (p.1 + (offset : ℤ), p.2)) := by
-- proof
  exact d.shift_toShape offset


-- created on 2026-10-20
