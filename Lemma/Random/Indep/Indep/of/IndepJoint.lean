import Mathlib.Probability.Independence.Basic
import sympy.stats.joint_rv
import sympy.Basic
open ProbabilityTheory MeasureTheory


@[main, And.left, And.right]
private lemma main
  {Ω α β γ : Type*}
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (h : (x, y) ⟂ᵢ[𝕡] z) :
-- imply
  x ⟂ᵢ[𝕡] z ∧ y ⟂ᵢ[𝕡] z :=
-- proof
  ⟨h.comp measurable_fst measurable_id, h.comp measurable_snd measurable_id⟩


-- created on 2026-09-19
