/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Analysis.SpecialFunctions.Part1Ch9Entry13Bernoulligen.Part2
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry13Bernoulligen

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Filter Finset Topology MeasureTheory

noncomputable section

/-! ## Abel regularization: definitions -/

/-- Abel denominator `D_r(u) = 1 - 2r cos u + r^2`. -/
def entry13D (r u : ℝ) : ℝ := 1 - 2 * r * Real.cos u + r ^ 2

/-- Closed form of the regularized `m = 1` Clausen sum. -/
def entry13c1closed (r x : ℝ) : ℝ := -(1 / 2) * Real.log (entry13D r x)

/-- Regularized Clausen sum `∑' k, r^(k+1) T_m(x,k)`. -/
def entry13cm (m : ℕ) (r x : ℝ) : ℝ :=
  ∑' k : ℕ, r ^ (k + 1) * chapter9ClausenTerm m x k

/-- Combined regularized value: closed form at `m = 1`, series otherwise. -/
def entry13C (m : ℕ) (r x : ℝ) : ℝ :=
  if m = 1 then entry13c1closed r x else entry13cm m r x

/-- Poisson-type kernel `K_r(u) = r sin u / D_r(u)`. -/
def entry13K (r u : ℝ) : ℝ := r * Real.sin u / entry13D r u

/-- Sign `s_j = (-1)^(j(j+1)/2)`. -/
def entry13s (j : ℕ) : ℝ := (-1 : ℝ) ^ (j * (j + 1) / 2)

/-- Derivative sign: `+1` if `j+1` even, `-1` otherwise. -/
def entry13eps (j : ℕ) : ℝ := if Even (j + 1) then 1 else -1

end
end Entry13Bernoulligen
end Ramanujan.Part1Ch9
end
