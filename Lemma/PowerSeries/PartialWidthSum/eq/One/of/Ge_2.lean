import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[partial_width_sum_one_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (k : ℕ)
  (hk : k ≥ 2)
  (ts : Fin k → (Σ m : ℕ, Subtype (fun (T' : Tiling (Rectangle m 2)) => isFaultfree m T'))) :
-- imply
  partialWidthSum k ts ⟨1, by omega⟩ = (ts ⟨0, by omega⟩).1 := by
-- proof
  simp only [partialWidthSum, Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero, Fin.val_zero]


-- created on 2026-10-20
