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
import Def.Probability.LevyKhintchin.Part3
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

lemma lk_hasSum_poisson (lam : ℝ) :
    HasSum (fun n : ℕ ↦ Real.exp (-lam) * lam ^ n / (n.factorial : ℝ)) 1 := by
  have h := HasSum.mul_left (Real.exp (-lam)) (NormedSpace.expSeries_div_hasSum_exp lam)
  have h' : HasSum (fun n : ℕ ↦ Real.exp (-lam) * lam ^ n / (n.factorial : ℝ))
      (Real.exp (-lam) * NormedSpace.exp lam) := by
    refine h.congr_fun ?_
    intro n
    ring
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add] at h'
  simpa using h'

lemma lk_compound_term_univ (ρ : Measure ℝ) [IsFiniteMeasure ρ] (n : ℕ) :
    (lkPoissonCoeff ρ n • lkConvPow ρ n) Set.univ =
      ENNReal.ofReal
        (Real.exp (-ρ.real Set.univ) * (ρ.real Set.univ) ^ n / (n.factorial : ℝ)) := by
  rw [Measure.smul_apply, lkConvPow_apply_univ]
  simp only [smul_eq_mul, lkPoissonCoeff]
  let lam : ℝ := ρ.real Set.univ
  change ENNReal.ofReal (Real.exp (-lam) / (n.factorial : ℝ)) * (ρ Set.univ) ^ n =
    ENNReal.ofReal (Real.exp (-lam) * lam ^ n / (n.factorial : ℝ))
  have hmass : ρ Set.univ = ENNReal.ofReal lam :=
    (ENNReal.ofReal_toReal (measure_ne_top ρ Set.univ)).symm
  have hlam : 0 ≤ lam := ENNReal.toReal_nonneg
  rw [hmass, ← ENNReal.ofReal_pow hlam]
  rw [← ENNReal.ofReal_mul (by positivity :
    0 ≤ Real.exp (-lam) / (n.factorial : ℝ))]
  congr 1
  ring

lemma lk_compoundPoisson_probability (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
    IsProbabilityMeasure (lkCompoundPoisson ρ) := by
  rw [isProbabilityMeasure_iff, lkCompoundPoisson, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [lk_compound_term_univ]
  let lam : ℝ := ρ.real Set.univ
  change (∑' n : ℕ,
    ENNReal.ofReal (Real.exp (-lam) * lam ^ n / (n.factorial : ℝ))) = 1
  have hlam : 0 ≤ lam := ENNReal.toReal_nonneg
  have hsum := lk_hasSum_poisson lam
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hsum.summable, hsum.tsum_eq]
  norm_num

lemma lk_charFun_compoundPoisson_aux (ρ : Measure ℝ) [IsFiniteMeasure ρ] (t : ℝ) :
    charFun (lkCompoundPoisson ρ) t =
      Complex.exp (charFun ρ t - (ρ.real Set.univ : ℂ)) := by
  let _ := lk_compoundPoisson_probability ρ
  have h_integrable : Integrable (BoundedContinuousFunction.innerProbChar t)
      (lkCompoundPoisson ρ) :=
    (BoundedContinuousFunction.innerProbChar t).integrable _
  rw [charFun_eq_integral_innerProbChar, lkCompoundPoisson]
  rw [integral_sum_measure h_integrable]
  simp_rw [integral_smul_measure, ← charFun_eq_integral_innerProbChar,
    lk_charFun_convPow, lkPoissonCoeff_toReal, Complex.real_smul]
  let lam : ℝ := ρ.real Set.univ
  let z : ℂ := charFun ρ t
  change (∑' n : ℕ, ((Real.exp (-lam) / (n.factorial : ℝ) : ℝ) : ℂ) * z ^ n) =
    Complex.exp (z - (lam : ℂ))
  have h := HasSum.mul_left (Real.exp (-lam) : ℂ)
    (NormedSpace.expSeries_div_hasSum_exp z)
  have h' : HasSum
      (fun n : ℕ ↦ ((Real.exp (-lam) / (n.factorial : ℝ) : ℝ) : ℂ) * z ^ n)
      (Real.exp (-lam) * NormedSpace.exp z) := by
    refine h.congr_fun ?_
    intro n
    push_cast
    ring
  rw [Complex.ofReal_exp, ← Complex.exp_eq_exp_ℂ, ← Complex.exp_add] at h'
  rw [h'.tsum_eq]
  congr 1
  push_cast
  ring

lemma lk_charFun_compoundPoisson (ρ : Measure ℝ) [IsFiniteMeasure ρ] (t : ℝ) :
    charFun (lkCompoundPoisson ρ) t =
      Complex.exp (∫ x, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 ∂ρ) := by
  rw [lk_charFun_compoundPoisson_aux]
  congr 1
  have h_fun :
      (fun x : ℝ ↦ Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) =
        fun x : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) := by
    funext x
    congr 1
    ring
  rw [charFun_apply_real, h_fun]
  rw [integral_sub (lk_integrable_exp_mul_I ρ t) (integrable_const 1)]
  rw [integral_const]
  simp [Complex.real_smul]

end MetaMathlibExt
