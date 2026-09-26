import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import sympy.Basic
open MeasureTheory ProbabilityTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ι : Type*}
  {L : Ω → ι}
  {i : ι}
-- given
  (h₀ : μ {ω | L ω = i} ≠ 0)
  (g : ι → ℝ) :
-- imply
  ∫ ω, g (L ω) ∂μ[|{ω | L ω = i}] = g i := by
-- proof
  have := cond_isProbabilityMeasure h₀
  rw [integral_congr_ae ((ae_cond_mem (s := {ω | L ω = i}) .of_discrete).mono fun ω (hω : L ω = i) => congrArg g hω), integral_const, probReal_univ, one_smul]


-- created on 2026-09-26
