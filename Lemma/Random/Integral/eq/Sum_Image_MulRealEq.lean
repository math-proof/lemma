import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
-- given
  (X : Ω → ℝ) :
-- imply
  ∫ ω, X ω ∂μ = ∑ y ∈ Finset.univ.image X, μ.real {ω | X ω = y} * y := by
-- proof
  classical
  rw [integral_fintype .of_finite, ← Finset.sum_fiberwise_of_maps_to (g := X) (t := Finset.univ.image X) fun ω _ => Finset.mem_image_of_mem X (Finset.mem_univ ω)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_congr rfl fun ω hω => by rw [(Finset.mem_filter.mp hω).2], ← Finset.sum_smul, smul_eq_mul, sum_measureReal_singleton]
  congr 2
  ext
  simp


-- created on 2026-09-26
