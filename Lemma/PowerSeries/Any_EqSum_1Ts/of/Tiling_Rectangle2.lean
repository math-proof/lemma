import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[tiling_decomposition_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2)) :
-- imply
  ∃ (k : ℕ) (ts : Fin k → Σ m, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T')),
        (∑ i, (ts i).1) = n := by
-- proof
  exact ⟨(decomposeTiling n T).1, (decomposeTiling n T).2, decomposeTiling_weight_sum n T⟩


-- created on 2026-10-20
