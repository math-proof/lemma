import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[domino_shift_injective_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (offset : ℤ) :
-- imply
  Function.Injective (fun d : Domino => d.shift offset) := by
-- proof
  intro d1 d2 h
  cases d1 <;> cases d2 <;> simp only [shift, Domino.horizontal.injEq, Domino.vertical.injEq] at h ⊢
  · omega
  · contradiction
  · contradiction
  · omega


-- created on 2026-10-20
