import Syntax.Probability.Expectation.Elab
import Instance.Analysis.Real.Numbers
import Lemma.Random.Map.eq.WithDensityProb
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
open MeasureTheory Random
open scoped ENNReal.ToRealCoe


/--
Continuous importance sampling: changing the sampling law from `π` to `π'`
reweights by the likelihood ratio of densities `ℙ[π](x) / ℙ[π'](x)`
(observation / pdf form `ℙ[π](x = ·)`, not a conditional `ℙ[π](· | ·)`).
Requires the target density under `π` to vanish a.e. wherever the proposal
density under `π'` vanishes (absolute continuity of the pushforwards).
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [μ : ReferenceMeasure α]
  [NormedAddCommGroup ℰ] [NormedSpace ℝ ℰ] [CompleteSpace ℰ] [MeasurableSpace ℰ] [BorelSpace ℰ]
  {x : Ω → α} {f : α → ℰ}
  {π : Measure Ω} [SinglePSpace π x]
  {π' : Measure Ω} [SinglePSpace π' x]
-- given
  (hf : Measurable f)
  (habs : ∀ᵐ «\sf{x}» ∂μ.measure,
    ℙ[π'](x = «\sf{x}») = 0 → ℙ[π](x = «\sf{x}») = 0) :
-- imply
  𝔼[x: π](f x) = 𝔼[x: π'](((ℙ[π](x) / ℙ[π'](x)) : ℝ) • f x) := by
-- proof
  have hp : Measurable (π.prob x) := Measure.measurable_rnDeriv _ _
  have hp' : Measurable (π'.prob x) := Measure.measurable_rnDeriv _ _
  have hratio : Measurable fun «\sf{x}» ↦ π.prob x «\sf{x}» / π'.prob x «\sf{x}» :=
    hp.div hp'
  have htop : ∀ᵐ «\sf{x}» ∂μ.measure, π.prob x «\sf{x}» ≠ ⊤ :=
    Measure.rnDeriv_ne_top _ _
  have htop' : ∀ᵐ «\sf{x}» ∂μ.measure, π'.prob x «\sf{x}» ≠ ⊤ :=
    Measure.rnDeriv_ne_top _ _
  simp only [Expectation.asRV_function, Expectation.ofRV, expectation_bochner]
  rw [Map.eq.WithDensityProb (π := π) (x := x),
    Map.eq.WithDensityProb (π := π') (x := x)]
  have hmul :
    (fun «\sf{x}» ↦ π'.prob x «\sf{x}» * (π.prob x «\sf{x}» / π'.prob x «\sf{x}»)) =ᵐ[μ.measure]
      π.prob x := by
    filter_upwards [habs, htop'] with «\sf{x}» hs hsTop
    exact (mul_comm _ _).trans
      (ENNReal.div_mul_cancel'
        (fun h0 ↦ by
          have := hs h0
          simp [this])
        fun hTop ↦ (hsTop hTop).elim)
  have hdens :
    μ.measure.withDensity (π.prob x) =
      (μ.measure.withDensity (π'.prob x)).withDensity
        fun «\sf{x}» ↦ π.prob x «\sf{x}» / π'.prob x «\sf{x}» := by
    rw [← withDensity_congr_ae hmul]
    exact withDensity_mul μ.measure hp' hratio
  have hratio_lt_top :
    ∀ᵐ «\sf{x}» ∂μ.measure.withDensity (π'.prob x),
      π.prob x «\sf{x}» / π'.prob x «\sf{x}» < (⊤ : ENNReal) := by
    rw [ae_withDensity_iff hp']
    filter_upwards [htop] with «\sf{x}» ht hp'0
    exact ENNReal.div_lt_top ht hp'0
  have := hf
  rw [hdens, integral_withDensity_eq_integral_toReal_smul hratio hratio_lt_top]
  refine integral_congr_ae ?_
  filter_upwards with «\sf{x}»
  rw [ENNReal.toReal_div]


-- created on 2023-03-25
-- updated on 2026-11-14
