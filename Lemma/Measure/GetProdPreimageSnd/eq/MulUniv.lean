import Mathlib.MeasureTheory.Measure.Prod
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α}
  {ν : Measure β} [SFinite ν]
-- given
  (A : Set β) :
-- imply
  (μ.prod ν) (Prod.snd ⁻¹' A) = μ Set.univ * ν A := by
-- proof
  rw [show Prod.snd ⁻¹' A = (Set.univ : Set α) ×ˢ A by ext; simp, Measure.prod_prod]


-- created on 2026-09-26