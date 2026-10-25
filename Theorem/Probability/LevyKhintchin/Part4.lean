/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LevyKhintchin.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Def.Probability.LevyKhintchin.Part4
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

lemma lk_compensation_integrable {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (k : ℕ) :
    Integrable (Set.indicator {y : ℝ | |y| ≤ 1} id) (lkTruncate ν k) := by
  let _ := lk_restrict_away_zero_finite hν k
  have h_meas : StronglyMeasurable (Set.indicator {y : ℝ | |y| ≤ 1} id) :=
    stronglyMeasurable_id.indicator <| (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  apply Integrable.of_bound h_meas.aestronglyMeasurable 1
  exact ae_of_all _ fun x ↦ by
    by_cases hx : |x| ≤ 1
    · rw [Set.indicator_of_mem (show x ∈ {y : ℝ | |y| ≤ 1} from hx)]
      simpa [Real.norm_eq_abs] using hx
    · rw [Set.indicator_of_notMem (show x ∉ {y : ℝ | |y| ≤ 1} from hx)]
      simp

lemma lk_linear_integrable_truncate {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (k : ℕ) (t : ℝ) :
    Integrable (Set.indicator {y : ℝ | |y| ≤ 1}
      (fun y ↦ Complex.I * (t : ℂ) * (y : ℂ))) (lkTruncate ν k) := by
  have h := (lk_compensation_integrable hν k).ofReal.const_mul
    (Complex.I * (t : ℂ))
  refine h.congr (ae_of_all _ fun x ↦ ?_)
  by_cases hx : |x| ≤ 1 <;> simp [hx]

lemma lk_integral_jump_truncate {ν : Measure ℝ}
    (hν : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ∞) (k : ℕ) (t : ℝ) :
    (∫ x, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 ∂lkTruncate ν k) -
        Complex.I * (t : ℂ) * (lkCompensation ν k : ℂ) =
      ∫ x, lkJump t x ∂lkTruncate ν k := by
  let _ := lk_restrict_away_zero_finite hν k
  have h_exp := lk_integrable_exp_mul_I (lkTruncate ν k) t
  have h_sub : Integrable
      (fun x : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1)
      (lkTruncate ν k) := h_exp.sub (integrable_const 1)
  rw [← lk_integral_compensation ν k t]
  rw [← integral_sub h_sub (lk_linear_integrable_truncate hν k t)]
  rfl

end MetaMathlibExt
