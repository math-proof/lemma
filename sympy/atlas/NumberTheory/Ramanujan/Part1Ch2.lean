/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lemma.Nat.Ramanujan.Part1Ch2Entry3
section
/-!
# Ramanujan's Notebooks, Part I, Chapter 2

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry3InfiniteEvaluation

open Real Filter Topology intervalIntegral

/-- `arctan (1/k)`, the summand of the moving-window reformulation. -/
private noncomputable def g (k : ℕ) : ℝ := arctan (1 / (k : ℝ))

/-- The summand of the series. -/
private noncomputable def f (n : ℕ) : ℝ :=
  arctan (10 * ((n : ℝ) + 1) / ((3 * ((n : ℝ) + 1) ^ 2 + 2) * (9 * ((n : ℝ) + 1) ^ 2 - 1)))
end Entry3InfiniteEvaluation
end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
