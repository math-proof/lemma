import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[decompose_tiling_faultfree_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle (n + 1) 2))
  (hff : isFaultfree (n + 1) T) :
-- imply
  decomposeTiling (n + 1) T = ⟨1, fun _ => ⟨n + 1, ⟨T, hff⟩⟩⟩ := by
-- proof
  unfold decomposeTiling
  -- Since T is faultfree, faultPositions is empty, so Nonempty is false
  have hne : ¬(faultPositions (n + 1) T).Nonempty := 
    faultPositions_not_nonempty_of_isFaultfree (n + 1) T hff
  simp only [dite_eq_right hne]


-- created on 2026-10-20
