import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[partial_width_sum_zero_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k : ℕ)
  (i : Fin k)
  (hi : i.val = 0)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  partialWidthSum k ts i = 0 := by
-- proof
  simp only [partialWidthSum]
  have hempty : (Finset.univ : Finset (Fin i.val)) = ∅ := by rw [hi]; rfl
  simp [hempty]


-- created on 2026-10-20
