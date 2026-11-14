import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Lemma.Random.Map.eq.WithDensityProb
import Syntax.Probability.Expectation.Elab
import Instance.Analysis.Real.Numbers
open MeasureTheory ProbabilityTheory Random
open scoped ENNReal.ToRealCoe


@[path]
private lemma main
  [MeasurableSpace Ω]
  [μ : ReferenceMeasure α]
  [NormedAddCommGroup ℰ] [NormedSpace ℝ ℰ] [CompleteSpace ℰ] [MeasurableSpace ℰ] [BorelSpace ℰ]
  {π : Measure Ω} {a : Ω → α} {f : α → ℰ}
-- given
  (hP : SinglePSpace π a)
  (hf : Measurable f) :
-- imply
  𝔼[a: π](f a) =
    ∫ «\sf{a}», (ℙ[π](a = «\sf{a}») : ℝ) • f «\sf{a}» ∂μ.measure := by
-- proof
  have := hf
  simp only [Expectation.asRV_function, Expectation.ofRV, expectation_bochner]
  have hmp : Measurable (π.prob a) :=
    Measure.measurable_rnDeriv (π.map a) μ.measure
  have hlt : ∀ᵐ «\sf{a}» ∂μ.measure, π.prob a «\sf{a}» < ⊤ :=
    (Measure.rnDeriv_ne_top (π.map a) μ.measure).mono fun _ h => h.lt_top
  rw [Map.eq.WithDensityProb, integral_withDensity_eq_integral_toReal_smul hmp hlt]


-- created on 2023-03-24
-- updated on 2026-11-14
