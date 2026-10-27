import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet


/--
[tuples_weight_eq_pow_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  {α : Type*}
  (W : WeightedSet α)
  (n : ℕ)
  (f : Fin n → α) :
-- imply
  W.tuples.weight ⟨n, f⟩ = (W.pow n).weight f := by
-- proof
  simp only [tuples, pow]


-- created on 2026-10-20
