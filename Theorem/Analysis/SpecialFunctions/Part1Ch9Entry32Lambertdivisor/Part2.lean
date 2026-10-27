/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry32Lambertdivisor.Part2
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


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
