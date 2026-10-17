import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import sympy.Basic
open MeasureTheory ProbabilityTheory


/--
Reward given a realized next-state atom: conditioning on `{a}` with positive mass returns `ρ a`.
-/
@[path]
private lemma main
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure ι} [IsFiniteMeasure μ]
  {a : ι}
  (ρ : ι → ℝ)
-- given
  (h₀ : μ {a} ≠ 0) :
-- imply
  ∫ i, ρ i ∂μ[|{a}] = ρ a := by
-- proof
  have hdirac : μ[|{a}] = Measure.dirac a := by
    refine Measure.ext fun s hs => ?_
    rw [cond_apply (measurableSet_singleton a), Measure.dirac_apply' _ hs]
    if ha : a ∈ s then
      simp [ha, Set.inter_comm, ENNReal.inv_mul_cancel h₀ (measure_ne_top μ _)]
    else
      simp [ha]
  rw [hdirac, integral_dirac]


-- created on 2026-10-11
-- updated on 2026-10-17
