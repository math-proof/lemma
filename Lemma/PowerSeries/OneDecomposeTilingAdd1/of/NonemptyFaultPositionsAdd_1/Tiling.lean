import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[decompose_tiling_has_fault_fst_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle (n + 1) 2))
  (hne : (faultPositions (n + 1) T).Nonempty) :
-- imply
  let k := minFault (n + 1) T hne
  let hk := minFault_hasFault (n + 1) T hne
  let right := restrictTilingRight (n + 1) T k hk
  (decomposeTiling (n + 1) T).1 = (decomposeTiling (n + 1 - k) right).1 + 1 := by
-- proof
  simp only [decomposeTiling, dite_eq_left hne]


-- created on 2026-10-20
