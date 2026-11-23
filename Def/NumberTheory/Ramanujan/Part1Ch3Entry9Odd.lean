/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry9Odd.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Defs.Filter
public import Def.NumberTheory.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
public import Theorem.Nat.Ramanujan.Part1Ch3Entry9IiGeneralizedbellgeneratingDefining
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.Order

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

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
