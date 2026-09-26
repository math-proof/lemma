import Mathlib.MeasureTheory.Measure.Prod
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure α} {X : α → β} {C : β}
  {Y : α → γ} [SFinite (μ.map Y)]
-- given
  (h₀ : ∀ᵐ a ∂μ, X a = C)
  (h₁ : Measurable Y) :
-- imply
  μ.map (fun a => (X a, Y a)) = (Measure.dirac C).prod (μ.map Y) := by
-- proof
  rw [Measure.map_congr (g := fun a => (C, Y a)) (h₀.mono fun a ha => by simp [ha]), Measure.dirac_prod, Measure.map_map (by fun_prop) h₁]
  rfl


-- created on 2026-09-26