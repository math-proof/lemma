/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 6

The convergent-series extension `F(x) = ∑_{k ≥ 1} f(k) - ∑_{k ≥ 1} f(k + x)` of the partial sums
of `f` satisfies `F(x) - F(x - 1) = f(x)` and agrees with the partial sums at natural numbers. Under
domination hypotheses its derivatives at `0` are `-∑_{k ≥ 1} f⁽ⁿ⁾(k)`, and when `F` is analytic at
`0` its Taylor series converges to it near `0`.
-/


namespace Ramanujan.Part1Ch6

namespace Entry6Harmonic

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology

noncomputable section

/-- The `k`-th term `f⁽q⁾(k + 1 + x)` of the shifted series of `q`-th derivatives of `f`. -/
def chapter6ShiftedDerivedSeriesTerm
    (f : ℝ → ℝ) (q : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  iteratedDeriv q f ((k : ℝ) + 1 + x)

/-- The constant `∑_{k ≥ 0} f⁽q⁾(k + 1)`: the shifted series of `q`-th derivatives at `x = 0`. -/
def chapter6DerivedSeriesConstant (f : ℝ → ℝ) (q : ℕ) : ℝ :=
  ∑' k : ℕ, chapter6ShiftedDerivedSeriesTerm f q 0 k

/-- Ramanujan's extension of the partial sums of `f` to real arguments,
`F(x) = ∑_{k ≥ 1} f(k) - ∑_{k ≥ 1} f(k + x)`. When the series converge it agrees with
`chapter6PartialSum f m` at `x = m` (`chapter6ConvergentSumExtension_natCast`). -/
def chapter6ConvergentSumExtension (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  chapter6DerivedSeriesConstant f 0 -
    ∑' k : ℕ, chapter6ShiftedDerivedSeriesTerm f 0 x k

/-- The `j`-th term `-c_{j+1} x^{j+1} / (j+1)!` of the Taylor series of
`chapter6ConvergentSumExtension f` at `0`, where `c_q = chapter6DerivedSeriesConstant f q`. -/
def chapter6Entry6Term
    (f : ℝ → ℝ) (x : ℝ) (j : ℕ) : ℝ :=
  -chapter6DerivedSeriesConstant f (j + 1) * x ^ (j + 1) /
    ((j + 1).factorial : ℝ)

/-- The partial sum `f 1 + f 2 + ⋯ + f x`. -/
def chapter6PartialSum (f : ℝ → ℝ) (x : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 x, f k

end
end Entry6Harmonic
end Ramanujan.Part1Ch6
