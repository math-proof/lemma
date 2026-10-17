import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import sympy.Basic
open MeasureTheory


/--
Expected reward on a finite sample space: `∫ ρ dμ = ∑ ρ i · P(i)`, the state-action backup.
-/
@[path]
private lemma main
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype ι]
  {μ : Measure ι} [IsFiniteMeasure μ]
  (ρ : ι → ℝ) :
-- imply
  ∫ i, ρ i ∂μ = ∑ i, μ.real {i} * ρ i := by
-- proof
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [measureReal_def, smul_eq_mul, mul_comm]


-- created on 2026-10-11
-- updated on 2026-10-17
