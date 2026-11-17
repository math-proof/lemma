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
public import Def.Analysis.SpecialFunctions.Part1Ch9Entry13Bernoulligen

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

theorem chapter9ClausenTerm_base_pos (m : ℕ) (k : ℕ) :
    (0 : ℝ) < ((((k + 1 : ℕ)) : ℝ) ^ m) := by
  apply pow_pos
  have hcast : ((((k + 1 : ℕ))) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hnn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  linarith

/-- Norm bound for the Clausen summand: `‖term‖ ≤ 1 / (k+1)^m`. -/
theorem chapter9ClausenTerm_norm_bound (m : ℕ) (x : ℝ) (k : ℕ) :
    ‖chapter9ClausenTerm m x k‖ ≤ 1 / ((((k + 1 : ℕ)) : ℝ) ^ m) := by
  have hpos := chapter9ClausenTerm_base_pos m k
  unfold chapter9ClausenTerm
  split_ifs with h
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (le_of_lt hpos)
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (le_of_lt hpos)

theorem chapter9ClausenTerm_shift_summable (m : ℕ) (hm : 2 ≤ m) :
    Summable (fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ m)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ m)) :=
    (Real.summable_one_div_nat_pow).mpr (by omega)
  exact (summable_nat_add_iff 1).mpr h

/-- The Clausen series is summable for `2 ≤ m`. -/
theorem chapter9ClausenTerm_summable_of_two_le (m : ℕ) (x : ℝ) (hm : 2 ≤ m) :
    Summable (chapter9ClausenTerm m x) :=
  Summable.of_norm_bounded (chapter9ClausenTerm_shift_summable m hm)
    (chapter9ClausenTerm_norm_bound m x)

/-- `chapter9Clausen` at `m = 0` vanishes. -/
theorem chapter9Clausen_zero (x : ℝ) : chapter9Clausen 0 x = 0 := by
  rfl

/-- `chapter9Clausen` at `m = 1` is the log-sine closed form. -/
theorem chapter9Clausen_one (x : ℝ) :
    chapter9Clausen 1 x = -Real.log |2 * Real.sin (x / 2)| := by
  rfl

/-- `chapter9Clausen` for `2 ≤ m` is the Clausen series. -/
theorem chapter9Clausen_of_two_le (m : ℕ) (x : ℝ) (hm : 2 ≤ m) :
    chapter9Clausen m x = ∑' k : ℕ, chapter9ClausenTerm m x k := by
  unfold chapter9Clausen
  split_ifs with h0 h1
  · omega
  · omega
  · rfl

end
end Entry13Bernoulligen
end Ramanujan.Part1Ch9
end
