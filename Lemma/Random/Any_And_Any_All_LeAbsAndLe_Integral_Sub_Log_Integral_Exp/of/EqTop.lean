import Lemma.Random.Any_And_Any_All_LeAbsAndLe_Integral_Sub_Log_Integral_Exp.of.Not
import Lemma.Random.Any_And_Any_All_LeAbsAndLe_Integral_Sub_Log_Integral_Exp.of.NotIntegrable_Llr
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Initialize.Tactic.Attr.Basic
open InformationTheory MeasureTheory Random Real


/--
If the Kullback–Leibler divergence is infinite, a bounded continuous test function makes the
Donsker–Varadhan expression larger than any prescribed real. The obstruction is either a singular
part or a non-integrable log-likelihood ratio, and both are visible to continuous functions.
-/
@[path]
private lemma main
  [TopologicalSpace α] [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
-- given
  (h : klDiv ν μ = ⊤)
  (M : ℝ) :
-- imply
  ∃ f : α → ℝ, Continuous f ∧ (∃ C, ∀ x, |f x| ≤ C) ∧ M ≤ ∫ x, f x ∂ν - log (∫ x, exp (f x) ∂μ) :=
-- proof
by
  if hνμ : ν ≪ μ then
    exact Any_And_Any_All_LeAbsAndLe_Integral_Sub_Log_Integral_Exp.of.NotIntegrable_Llr hνμ
      ((klDiv_eq_top_iff).mp h hνμ) M
  else
    exact Any_And_Any_All_LeAbsAndLe_Integral_Sub_Log_Integral_Exp.of.Not hνμ M


-- created on 2026-11-02
