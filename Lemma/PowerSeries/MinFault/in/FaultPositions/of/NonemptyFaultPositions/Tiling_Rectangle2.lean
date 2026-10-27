import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[min_fault_mem_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : Tiling (Rectangle n 2))
  (hne : (faultPositions n T).Nonempty) :
-- imply
  minFault n T hne ∈ faultPositions n T := by
-- proof
  unfold minFault
  have := (faultPositions_finite n T).toFinset.min'_mem (by
    rw [Set.Finite.toFinset_nonempty]; exact hne)
  simp only [Set.Finite.mem_toFinset] at this
  exact this


-- created on 2026-10-20
