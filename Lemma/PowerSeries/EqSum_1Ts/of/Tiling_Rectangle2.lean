import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[decompose_tiling_weight_sum_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2)) :
-- imply
  let ⟨k, ts⟩ := decomposeTiling n T
  (∑ i : Fin k, (ts i).1) = n := by
-- proof
  simp only
  have h1 := composeTilings_decomposeTiling n T
  simp only at h1
  have h2 := composeTilings_width (decomposeTiling n T).1 (decomposeTiling n T).2
  rw [← h2]
  exact congrArg Sigma.fst h1


-- created on 2026-10-20
