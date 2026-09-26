import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ι : Type*} [Fintype ι]
-- given
  (L : Ω → ι)
  (g : ι → ℝ) :
-- imply
  ∫ ω, g (L ω) ∂μ = ∑ i, μ.real {ω | L ω = i} * g i := by
-- proof
  classical
  rw [integral_fintype .of_finite, ← Finset.sum_fiberwise Finset.univ L]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl fun ω hω => by rw [(Finset.mem_filter.mp hω).2], ← Finset.sum_smul, smul_eq_mul, sum_measureReal_singleton]
  congr 2
  ext
  simp


-- created on 2026-09-26
