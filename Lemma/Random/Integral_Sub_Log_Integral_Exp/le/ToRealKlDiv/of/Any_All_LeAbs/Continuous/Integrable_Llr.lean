import Lemma.Random.Integral_Sub_Log_Integral_Exp.le.ToRealKlDiv.of.Any_All_LeAbs.Measurable.Integrable_Llr
import Initialize.Tactic.Attr.Basic
open InformationTheory MeasureTheory Random Real


/--
A bounded continuous test function obeys the same Donsker–Varadhan upper bound as a bounded
measurable one. On a Borel space continuity supplies measurability, so the expression stays at most
the Kullback–Leibler divergence.
-/
@[path]
private lemma main
  [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {f : α → ℝ}
-- given
  (hνμ : ν ≪ μ)
  (hint : Integrable (llr ν μ) ν)
  (hf : Continuous f)
  (hC : ∃ C, ∀ x, |f x| ≤ C) :
-- imply
  ∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ) ≤ (klDiv ν μ).toReal :=
-- proof
  Integral_Sub_Log_Integral_Exp.le.ToRealKlDiv.of.Any_All_LeAbs.Measurable.Integrable_Llr hνμ hint hf.measurable hC


-- created on 2026-11-02
