/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry13Bernoulligen.lean -/

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
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry13Bernoulligen

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Filter Finset Topology MeasureTheory

noncomputable section

def chapter9ClausenTerm (m : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  if Even m then
    Real.sin (((k + 1 : ℕ) : ℝ) * x) / (((k + 1 : ℕ) : ℝ) ^ m)
  else
    Real.cos (((k + 1 : ℕ) : ℝ) * x) / (((k + 1 : ℕ) : ℝ) ^ m)

def chapter9Clausen (m : ℕ) (x : ℝ) : ℝ :=
  if m = 0 then 0
  else if m = 1 then -Real.log |2 * Real.sin (x / 2)|
  else ∑' k : ℕ, chapter9ClausenTerm m x k

def chapter9Entry13Integrand (n : ℕ) (u : ℝ) : ℝ :=
  u ^ n / 2 * (Real.cos (u / 2) / Real.sin (u / 2))

def entry13F0 (n : ℕ) : ℝ := if n = 1 then 1 else 0

def entry13Ext (n : ℕ) (u : ℝ) : ℝ :=
  if u = 0 then entry13F0 n else chapter9Entry13Integrand n u

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

/-! ## Helper H1: the log series (the only complex step) -/

/-- The complex point `w = r e^{ix}`. -/
def entry13w (r x : ℝ) : ℂ := (r : ℂ) * Complex.exp ((x : ℂ) * Complex.I)

/-- Derivative value of `C_{j+1}`: `-K` at `j = 0`, `eps*C_j` otherwise. -/
def entry13Cp (j : ℕ) (r x : ℝ) : ℝ :=
  if j = 0 then -entry13K r x else entry13eps j * entry13C j r x

def entry13G (n : ℕ) (r x : ℝ) : ℝ :=
  -∑ j ∈ Finset.range (n + 1),
    entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
      * x ^ (n - j) * entry13C (j + 1) r x

end
end Entry13Bernoulligen
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
