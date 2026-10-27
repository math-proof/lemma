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
import Def.Analysis.SpecialFunctions.Part1Ch9Entry32Lambertdivisor.Part8
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

theorem s32_of_t_zero : s32_of_t 0 = 0 := by
  unfold s32_of_t
  norm_num

theorem abs_s32_of_t_lt_one {t : ℝ} (ht : ‖t‖ < 1) :
    ‖s32_of_t t‖ < 1 := by
  have habs : |t| < 1 := by
    rw [← Real.norm_eq_abs]
    exact ht
  have hDpos : (0:ℝ) < 1 + t ^ 2 := by positivity
  have hSq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have h1 : 2 * |t| < 1 + t ^ 2 := by
    have hsq : (0:ℝ) < (1 - |t|) ^ 2 := by
      have hpos : (0:ℝ) < 1 - |t| := by linarith [habs]
      exact sq_pos_of_ne_zero (ne_of_gt hpos)
    have hexpand : (1 - |t|) ^ 2 = 1 - 2 * |t| + |t| ^ 2 := by ring
    rw [hexpand] at hsq
    rw [← hSq] at hsq
    linarith [hsq]
  have hAbs : |s32_of_t t| = 2 * |t| / (1 + t ^ 2) := by
    unfold s32_of_t
    rw [abs_div, abs_of_pos hDpos]
    congr 1
    rw [abs_mul]
    norm_num
  rw [Real.norm_eq_abs, hAbs]
  rw [div_lt_one hDpos]
  exact h1

theorem hasDerivAt_s32_of_t (t : ℝ) :
    HasDerivAt s32_of_t (2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2) t := by
  have h1 : HasDerivAt (fun w : ℝ => 2 * w) 2 t := by
    have h := hasDerivAt_id' t
    have h2 := h.const_mul (2:ℝ)
    simpa using h2
  have h2 : HasDerivAt (fun w : ℝ => (1:ℝ) + w ^ 2) (2 * t) t := by
    have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * t) t := by
      have h := hasDerivAt_pow 2 t
      simpa using h
    have hc := hp.const_add (1:ℝ)
    simpa [add_comm] using hc
  have hDne : (1:ℝ) + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hdiv := h1.div h2 hDne
  have hval : (2 * (1 + t ^ 2) - 2 * t * (2 * t)) / (1 + t ^ 2) ^ 2
      = 2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2 := by ring
  rw [hval] at hdiv
  exact hdiv

theorem sqrt_one_sub_s32_sq {t : ℝ} (ht : ‖t‖ < 1) :
    √(1 - (s32_of_t t) ^ 2) = (1 - t ^ 2) / (1 + t ^ 2) := by
  have habs : |t| < 1 := by
    rw [← Real.norm_eq_abs]
    exact ht
  have hDpos : (0:ℝ) < 1 + t ^ 2 := by positivity
  have hNpos : (0:ℝ) < 1 - t ^ 2 := by
    have hsq : t ^ 2 < 1 := by
      have hmem := abs_lt.mp habs
      have hsq2 : t ^ 2 < 1 ^ 2 := sq_lt_sq' hmem.1 hmem.2
      simpa using hsq2
    linarith [hsq]
  have hEq : 1 - (s32_of_t t) ^ 2
      = ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 := by
    unfold s32_of_t
    field_simp
    ring
  rw [hEq, Real.sqrt_sq (by positivity)]

theorem arcsin_s32_eq {t : ℝ} (ht : ‖t‖ < 1) :
    Real.arcsin (s32_of_t t) = 2 * Real.arctan t := by
  have habs : |t| < 1 := by
    rw [← Real.norm_eq_abs]
    exact ht
  have hmem := abs_lt.mp habs
  have h1 : Real.arctan (-1) < Real.arctan t := by
    rw [Real.arctan_lt_arctan_iff]
    exact hmem.1
  have h2 : Real.arctan t < Real.arctan 1 := by
    rw [Real.arctan_lt_arctan_iff]
    exact hmem.2
  have ha1 : Real.arctan (1:ℝ) = Real.pi / 4 := Real.arctan_one
  have haN1 : Real.arctan (-1 : ℝ) = -(Real.pi / 4) := by
    rw [Real.arctan_neg, ha1]
  rw [haN1] at h1
  rw [ha1] at h2
  have hy1 : -(Real.pi / 2) ≤ 2 * Real.arctan t := by linarith [h1]
  have hy2 : 2 * Real.arctan t ≤ Real.pi / 2 := by linarith [h2]
  have hsin : Real.sin (2 * Real.arctan t) = s32_of_t t := by
    have h2mul := Real.sin_two_mul (Real.arctan t)
    have hs := Real.sin_arctan t
    have hc := Real.cos_arctan t
    have hDpos : (0:ℝ) < 1 + t ^ 2 := by positivity
    have hsq : √(1 + t ^ 2) * √(1 + t ^ 2) = 1 + t ^ 2 :=
      Real.mul_self_sqrt hDpos.le
    have hne : √(1 + t ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hDpos)
    calc Real.sin (2 * Real.arctan t)
        = 2 * (t / √(1 + t ^ 2)) * (1 / √(1 + t ^ 2)) := by
          rw [h2mul, hs, hc]
      _ = 2 * t / (√(1 + t ^ 2) * √(1 + t ^ 2)) := by field_simp
      _ = 2 * t / (1 + t ^ 2) := by rw [hsq]
      _ = s32_of_t t := by unfold s32_of_t; ring
  have hEq : Real.arcsin (Real.sin (2 * Real.arctan t))
      = 2 * Real.arctan t :=
    Real.arcsin_sin hy1 hy2
  rw [hsin] at hEq
  exact hEq

end
end Entry32Lambertdivisor
end Ramanujan.Part1Ch9
end
