import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet WeightedSetExamples


/--
[positive_integers_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main :
-- imply
  PositiveIntegers.IsFiniteType := by
-- proof
  intro n
  -- The set {a : ℕ+ | a.val = n} has at most one element
  apply Set.Subsingleton.finite
  intro x hx y hy
  simp only [Set.mem_ofPred_eq, PositiveIntegers] at hx hy
  exact PNat.eq (hx.trans hy.symm)


-- created on 2026-10-20
