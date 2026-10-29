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
import Def.Probability.LevyKhintchin.Part15
open MeasureTheory
open scoped ENNReal NNReal MeasureTheory Topology

/-!
# The Lévy–Khintchin representation

This file proves the one-dimensional Lévy–Khintchin characterization of infinitely divisible
probability measures, with the hard truncation convention at radius one.
-/


namespace MetaMathlibExt

lemma lk_integral_canonicalMeasure (rho : Measure ℝ)
    (hprob : IsProbabilityMeasure rho) (n : ℕ) (t : ℝ) :
    (∫ x, lkCanonicalIntegrand t x ∂(lkCanonicalMeasure rho hprob n : Measure ℝ)) =
      ((n + 1 : ℕ) : ℂ) * ∫ x, lkSmoothJump t x ∂rho := by
  rw [lkCanonicalMeasure]
  change (∫ x, lkCanonicalIntegrand t x ∂
      ((n + 1 : NNReal) • (lkCanonicalBase rho hprob : Measure ℝ))) = _
  rw [integral_smul_nnreal_measure]
  change ((n + 1 : NNReal) : ℝ) •
      (∫ x, lkCanonicalIntegrand t x ∂rho.withDensity
        (fun x ↦ (lkCanonicalWeightNN x : ENNReal))) = _
  rw [show (fun x ↦ (lkCanonicalWeightNN x : ENNReal)) =
      fun x ↦ ((lkCanonicalWeightNN x : NNReal) : ENNReal) by rfl]
  have hweight : Measurable lkCanonicalWeightNN := by
    apply Continuous.measurable
    rw [show lkCanonicalWeightNN = fun x ↦ Real.toNNReal (lkCanonicalWeight x) by
      funext x
      rw [Real.toNNReal_of_nonneg (lkCanonicalWeight_nonneg x)]
      rfl]
    apply continuous_real_toNNReal.comp
    unfold lkCanonicalWeight
    exact (continuous_id.pow 2).div₀ (continuous_const.add (continuous_id.pow 2)) fun x : ℝ ↦ by
      positivity
  rw [integral_withDensity_eq_integral_smul hweight]
  simp only [NNReal.smul_def, Complex.real_smul]
  rw [show (∫ x, (lkCanonicalWeightNN x : ℝ) * lkCanonicalIntegrand t x ∂rho) =
      ∫ x, lkSmoothJump t x ∂rho by
        apply integral_congr_ae
        exact ae_of_all rho fun x ↦ lk_weight_mul_canonicalIntegrand t x]
  push_cast
  rfl

lemma lk_scaled_charFun_eq_drift_add_canonical (rho : Measure ℝ)
    (hprob : IsProbabilityMeasure rho) (n : ℕ) (t : ℝ) :
    ((n + 1 : ℕ) : ℂ) * (charFun rho t - 1) =
      Complex.I * (t : ℂ) * (lkDrift rho n : ℂ) +
        ∫ x, lkCanonicalIntegrand t x ∂(lkCanonicalMeasure rho hprob n : Measure ℝ) := by
  have hchar : charFun rho t - 1 =
      ∫ x, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 ∂rho := by
    rw [charFun_apply_real]
    rw [show (fun x : ℝ ↦ Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) =
        fun x : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) by
      funext x
      congr 1
      ring]
    rw [integral_sub (lk_integrable_exp_mul_I rho t) (integrable_const 1), integral_const]
    simp
  have hsplit : (∫ x, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 ∂rho) =
      Complex.I * (t : ℂ) * (∫ x, lkSmoothTruncation x ∂rho : ℝ) +
        ∫ x, lkSmoothJump t x ∂rho := by
    have hlinear : Complex.I * (t : ℂ) * (∫ x, lkSmoothTruncation x ∂rho : ℝ) =
        ∫ x, Complex.I * (t : ℂ) * (lkSmoothTruncation x : ℂ) ∂rho := by
      rw [integral_const_mul, integral_complex_ofReal]
    rw [hlinear]
    calc
      (∫ x, Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) - 1 ∂rho) =
          ∫ x, Complex.I * (t : ℂ) * (lkSmoothTruncation x : ℂ) +
            lkSmoothJump t x ∂rho := by
        apply integral_congr_ae
        exact ae_of_all rho fun x ↦ by
          unfold lkSmoothJump lkSmoothTruncation
          push_cast
          ring
      _ = _ := integral_add
        ((lk_smoothTruncation_integrable rho).ofReal.const_mul (Complex.I * (t : ℂ)))
        (lk_smoothJump_integrable rho t)
  rw [hchar, hsplit, mul_add, lk_integral_canonicalMeasure rho hprob n t]
  unfold lkDrift
  push_cast
  ring

lemma lk_tendsto_drift {rho : ℕ → Measure ℝ} {L : ℝ → ℂ}
    (hprob : ∀ n, IsProbabilityMeasure (rho n))
    (hroot : ∀ n t, charFun (rho n) t =
      Complex.exp (L t / ((n + 1 : ℕ) : ℝ)))
    {K : FiniteMeasure ℝ} {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ Filter.atTop)
    (hK : Filter.Tendsto
      (fun n ↦ lkCanonicalMeasure (rho n) (hprob n) n) U (nhds K)) :
    Filter.Tendsto (fun n ↦ lkDrift (rho n) n) U
      (nhds ((L 1 - ∫ x, lkCanonicalIntegrand 1 x ∂(K : Measure ℝ)).im)) := by
  have hscaled := (lk_scaled_charFun_sub_one_tendsto hroot 1).mono_left hU
  have hint := lk_tendsto_integral_canonicalIntegrand hK 1
  have hdiff := hscaled.sub hint
  have hI : Filter.Tendsto
      (fun n ↦ Complex.I * (lkDrift (rho n) n : ℂ)) U
      (nhds (L 1 - ∫ x, lkCanonicalIntegrand 1 x ∂(K : Measure ℝ))) := by
    convert hdiff using 1
    funext n
    rw [lk_scaled_charFun_eq_drift_add_canonical (rho n) (hprob n) n 1]
    push_cast
    ring
  have him := Complex.continuous_im.continuousAt.tendsto.comp hI
  have hfun : (Complex.im ∘ fun n ↦ Complex.I * (lkDrift (rho n) n : ℂ)) =
      fun n ↦ lkDrift (rho n) n := by
    funext n
    rw [Function.comp_apply, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hfun, Complex.sub_im] at him
  exact him

lemma lk_log_eq_drift_add_canonical {rho : ℕ → Measure ℝ} {L : ℝ → ℂ}
    (hprob : ∀ n, IsProbabilityMeasure (rho n))
    (hroot : ∀ n t, charFun (rho n) t =
      Complex.exp (L t / ((n + 1 : ℕ) : ℝ)))
    {K : FiniteMeasure ℝ} {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ Filter.atTop)
    (hK : Filter.Tendsto
      (fun n ↦ lkCanonicalMeasure (rho n) (hprob n) n) U (nhds K)) :
    ∃ b : ℝ, ∀ t : ℝ, L t = Complex.I * (t : ℂ) * (b : ℂ) +
      ∫ x, lkCanonicalIntegrand t x ∂(K : Measure ℝ) := by
  let b : ℝ := (L 1 - ∫ x, lkCanonicalIntegrand 1 x ∂(K : Measure ℝ)).im
  have hb : Filter.Tendsto (fun n ↦ lkDrift (rho n) n) U (nhds b) :=
    lk_tendsto_drift hprob hroot hU hK
  refine ⟨b, fun t ↦ ?_⟩
  have hscaled := (lk_scaled_charFun_sub_one_tendsto hroot t).mono_left hU
  have hint := lk_tendsto_integral_canonicalIntegrand hK t
  have hdrift : Filter.Tendsto
      (fun n ↦ Complex.I * (t : ℂ) * (lkDrift (rho n) n : ℂ)) U
      (nhds (Complex.I * (t : ℂ) * (b : ℂ))) :=
    hb.ofReal.const_mul (Complex.I * (t : ℂ))
  have hrhs := hdrift.add hint
  have hscaled' : Filter.Tendsto
      (fun n ↦ Complex.I * (t : ℂ) * (lkDrift (rho n) n : ℂ) +
        ∫ x, lkCanonicalIntegrand t x ∂
          (lkCanonicalMeasure (rho n) (hprob n) n : Measure ℝ)) U
      (nhds (L t)) := by
    refine hscaled.congr' (Filter.Eventually.of_forall fun n ↦ ?_)
    exact lk_scaled_charFun_eq_drift_add_canonical (rho n) (hprob n) n t
  exact tendsto_nhds_unique hscaled' hrhs

end MetaMathlibExt
