/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry6Corollary.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Parity

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
