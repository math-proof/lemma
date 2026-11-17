/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6Corollary.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Data.Rat.Star
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Parity

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Corollary to Entry 6

Harmonic sum from 1 equals r plus a weighted 27k³-3k reciprocal sum.
-/


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry6Corollary

/-- `A k = (3 ^ k - 1) / 2 = 1 + 3 + ⋯ + 3 ^ (k - 1)`. -/
def A (k : ℕ) : ℕ := (3 ^ k - 1) / 2

end Entry6Corollary
end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
