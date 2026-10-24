/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry9Odd.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Defs.Filter
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Lemma.Nat.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry9Odd

open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating
  ramanujan_part1_ch3_entry9_ii_generalizedbellgenerating_defining)

/-- Ramanujan's Entry 9(i) product series `P(a, b, x; z)`: the `j`-th summand is
`(-b)^j * x^(j+1)` divided by `∏ r ∈ Finset.range (j + 1), (z + a + b * (r + 1))`.

This is a totalized extension of the source expression: Lean's division sends `c / 0` to `0`,
and `∑'` of a non-summable family to `0`. Hence at a pole of the source expression -- for
example `a = 0`, `b = 1`, `x = 1`, `z = -1`, where every product contains the vanishing
factor `z + a + b * (0 + 1) = 0` -- every quotient, and so `entry9_P` itself, evaluates to
`0`, whereas the source expression has a singularity there. Off the poles, with
`w = (z + a) / b` in the sector `|arg w| ≤ π - ε` and `‖w‖ > 0`, `entry9_P_closed` identifies
`entry9_P` with the source's closed form. -/
noncomputable def entry9_P (a b x : ℂ) (z : ℂ) : ℂ :=
  ∑' (j : ℕ), ((-b) ^ j * x ^ (j + 1) / ∏ r ∈ Finset.range (j + 1), (z + a + b * ((r : ℂ) + 1)))
end Entry9Odd
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
