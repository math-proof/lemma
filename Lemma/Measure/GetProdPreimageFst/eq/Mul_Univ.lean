import Mathlib.MeasureTheory.Measure.Prod
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α}
  {ν : Measure β} [SFinite ν]
-- given
  (A : Set α) :
-- imply
  (μ.prod ν) (Prod.fst ⁻¹' A) = μ A * ν Set.univ := by
-- proof
  rw [show Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set β) by ext; simp, Measure.prod_prod]


-- created on 2026-09-26