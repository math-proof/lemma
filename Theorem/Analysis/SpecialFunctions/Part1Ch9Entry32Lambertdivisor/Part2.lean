/-
Author: @akiezun, Avocado
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.Analysis.SpecialFunctions.Part1Ch9Entry32Lambertdivisor.Part2

/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

public section


section

namespace Ramanujan.Part1Ch9

namespace Entry32Lambertdivisor

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem aCoeff32_nonneg (k : ℕ) : 0 ≤ aCoeff32 k := by
  unfold aCoeff32
  exact div_nonneg (le_of_lt (bCoeff32_pos k)) (Nat.cast_nonneg _)

theorem aCoeff32_zero : aCoeff32 0 = 1 := by
  unfold aCoeff32
  rw [bCoeff32_zero]
  norm_num

theorem aCoeff32_le (k : ℕ) :
    aCoeff32 k ≤ 2 * ((k : ℝ) + 1) := by
  unfold aCoeff32
  have hD : (1:ℝ) ≤ (((2 * k + 1 : ℕ)) : ℝ) := by
    have hle : 1 ≤ 2 * k + 1 := by omega
    exact_mod_cast hle
  have hDpos : (0:ℝ) < (((2 * k + 1 : ℕ)) : ℝ) := by positivity
  have hb := bCoeff32_le_two_succ k
  have hCnn : (0:ℝ) ≤ 2 * ((k : ℝ) + 1) := by positivity
  calc bCoeff32 k / (((2 * k + 1 : ℕ)) : ℝ)
      ≤ (2 * ((k : ℝ) + 1)) / (((2 * k + 1 : ℕ)) : ℝ) :=
        div_le_div_of_nonneg_right hb (le_of_lt hDpos)
    _ ≤ (2 * ((k : ℝ) + 1)) / 1 :=
        div_le_div_of_nonneg_left hCnn (by norm_num) hD
    _ = 2 * ((k : ℝ) + 1) := by ring

theorem aCoeff32_rec (k : ℕ) :
    (2 * (k : ℝ) + 3) * aCoeff32 (k + 1)
      = 2 * ((k : ℝ) + 1) * aCoeff32 k := by
  unfold aCoeff32
  rw [bCoeff32_succ]
  have hD1 : ((((2 * (k + 1) + 1 : ℕ))) : ℝ) = 2 * (k : ℝ) + 3 := by
    push_cast
    ring
  have hD0 : ((((2 * k + 1 : ℕ))) : ℝ) = 2 * (k : ℝ) + 1 := by
    push_cast
    ring
  rw [hD1, hD0]
  field_simp

end
end Entry32Lambertdivisor
end Ramanujan.Part1Ch9
end
