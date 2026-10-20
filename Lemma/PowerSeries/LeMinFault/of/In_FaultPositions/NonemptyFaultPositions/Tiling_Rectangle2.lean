import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[min_fault_le_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (j : ℕ)
  (hne : (faultPositions n T).Nonempty)
  (hj : j ∈ faultPositions n T) :
-- imply
  minFault n T hne ≤ j := by
-- proof
  unfold minFault
  apply (faultPositions_finite n T).toFinset.min'_le
  simp only [Set.Finite.mem_toFinset]
  exact hj


-- created on 2026-10-20
