import Mathlib.Analysis.Convex.Integral
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Initialize.Tactic.Attr.Basic
open ENNReal Filter InformationTheory MeasureTheory Real


private lemma variational_le [MeasurableSpace α] {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) (hint : Integrable (llr ν μ) ν) {f : α → ℝ} (hf : Measurable f) (hC : ∃ C, ∀ x, |f x| ≤ C) :
  ∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ) ≤ (klDiv ν μ).toReal := by
  obtain ⟨C, hC⟩ := hC
  have hfν : Integrable f ν :=
    Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hC x)
  have hexpμ : Integrable (fun x => exp (f x)) μ :=
    Integrable.of_bound (measurable_exp.comp hf).aestronglyMeasurable (exp C)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr (le_trans (le_abs_self _) (hC x)))
  have hle : ∀ x, (ν.rnDeriv μ x).toReal * exp (f x - llr ν μ x) ≤ exp (f x) := by
    intro x
    if h0 : (ν.rnDeriv μ x).toReal = 0 then
      simpa [h0, zero_mul] using (exp_pos (f x)).le
    else
      have hpos : 0 < (ν.rnDeriv μ x).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h0)
      simp [llr, exp_sub, exp_log hpos, mul_div_cancel₀ (exp (f x)) h0]
  have hprod : Integrable (fun x => (ν.rnDeriv μ x).toReal * exp (f x - llr ν μ x)) μ :=
    hexpμ.mono ((Measure.measurable_rnDeriv ν μ).ennreal_toReal.mul
      ((hf.sub ((Measure.measurable_rnDeriv ν μ).ennreal_toReal.log)).exp)).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs, abs_of_pos (exp_pos _)] using hle x)
  have hint_exp : Integrable (fun x => exp (f x - llr ν μ x)) ν :=
    (integrable_toReal_rnDeriv_mul_iff hνμ).mp hprod
  have hint_sub : Integrable (fun x => f x - llr ν μ x) ν := hfν.sub hint
  have h_int_le : ∫ x, exp (f x - llr ν μ x) ∂ν ≤ ∫ x, exp (f x) ∂μ := by
    refine le_of_eq_of_le (integral_toReal_rnDeriv_mul hνμ).symm ?_
    exact integral_mono hprod hexpμ hle
  have hJ : exp (∫ x, f x - llr ν μ x ∂ν) ≤ ∫ x, exp (f x - llr ν μ x) ∂ν :=
    convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
      (Eventually.of_forall fun _ => trivial) hint_sub hint_exp
  have hpos : 0 < ∫ x, exp (f x - llr ν μ x) ∂ν := integral_exp_pos hint_exp
  have hlog : ∫ x, f x - llr ν μ x ∂ν ≤ log (∫ x, exp (f x) ∂μ) :=
    (le_log_iff_exp_le (lt_of_lt_of_le hpos h_int_le)).mpr (hJ.trans h_int_le)
  rw [toReal_klDiv_of_measure_eq hνμ (by simp [measure_univ])]
  linarith [hlog, integral_sub hfν hint]

/--
A bounded measurable test function lies under the Kullback–Leibler divergence. The difference
between its integral and the logarithmic moment generating function of the reference measure is at
most the divergence. This is the upper bound in the Donsker–Varadhan formula for the rate of
Sanov's theorem.
-/
@[path]
private lemma main
  [MeasurableSpace α]
  {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {f : α → ℝ}
-- given
  (hνμ : ν ≪ μ)
  (hint : Integrable (llr ν μ) ν)
  (hf : Measurable f)
  (hC : ∃ C, ∀ x, |f x| ≤ C) :
-- imply
  ∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ) ≤ (klDiv ν μ).toReal :=
-- proof
  variational_le hνμ hint hf hC


-- created on 2026-11-02
