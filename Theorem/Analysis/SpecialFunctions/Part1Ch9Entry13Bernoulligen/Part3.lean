/-
Author: @akiezun, Avocado
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.Analysis.SpecialFunctions.Part1Ch9Entry13Bernoulligen.Part3

/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

public section


section

namespace Ramanujan.Part1Ch9

namespace Entry13Bernoulligen

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Filter Finset Topology MeasureTheory

noncomputable section

theorem entry13D_eq_sq (r u : ℝ) :
    entry13D r u = (1 - r) ^ 2 + 2 * r * (1 - Real.cos u) := by
  unfold entry13D
  ring

theorem entry13D_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (u : ℝ) :
    0 < entry13D r u := by
  rw [entry13D_eq_sq]
  have h1 : 0 < (1 - r) ^ 2 := by
    have : (0 : ℝ) < 1 - r := by linarith
    positivity
  have h2 : 0 ≤ 2 * r * (1 - Real.cos u) := by
    have hcos : Real.cos u ≤ 1 := Real.cos_le_one u
    have : (0 : ℝ) ≤ 1 - Real.cos u := by linarith
    positivity
  linarith

theorem entry13D_ne_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (u : ℝ) :
    entry13D r u ≠ 0 :=
  ne_of_gt (entry13D_pos hr0 hr1 u)

theorem entry13D_ge_two_mul (r u : ℝ) :
    2 * r * (1 - Real.cos u) ≤ entry13D r u := by
  rw [entry13D_eq_sq]
  have : (0 : ℝ) ≤ (1 - r) ^ 2 := sq_nonneg _
  linarith

/-- Half-angle identity `1 - cos u = 2 sin^2(u/2)`. -/
theorem entry13_one_sub_cos (u : ℝ) :
    1 - Real.cos u = 2 * Real.sin (u / 2) ^ 2 := by
  have h2 : u = 2 * (u / 2) := by ring
  conv_lhs => rw [h2, Real.cos_two_mul]
  have hsq := Real.sin_sq_add_cos_sq (u / 2)
  linarith

end
end Entry13Bernoulligen
end Ramanujan.Part1Ch9
end
