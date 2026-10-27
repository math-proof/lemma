import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Initialize.Tactic.Attr.Basic
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω}
  {X : Ω → S}
  {u v : S → β}
  {x : S}
-- given
  (h₀ : (fun ω ↦ u (X ω)) =ᵐ[π] fun ω ↦ v (X ω))
  (h₁ : π (X ⁻¹' {x}) ≠ 0) :
-- imply
  u x = v x := by
-- proof
  by_contra h
  apply h₁
  apply measure_mono_null _ (ae_iff.1 h₀)
  intro ω hω
  show ¬u (X ω) = v (X ω)
  rw [show X ω = x from hω]
  exact h


-- created on 2026-10-06
