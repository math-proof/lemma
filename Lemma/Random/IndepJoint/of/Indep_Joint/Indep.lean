import Mathlib.Probability.Independence.Basic
import sympy.stats.joint_rv
import Lemma.Random.IndepJoint.of.Indep.Indep_Joint
open ProbabilityTheory MeasureTheory Random


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
  [PSpace 𝕡 x] [PSpace 𝕡 y] [PSpace 𝕡 z]
-- given
  (hx : x ⟂ᵢ[𝕡] (y, z))
  (hy : y ⟂ᵢ[𝕡] z) :
-- imply
  (x, y) ⟂ᵢ[𝕡] z := by
-- proof
  have h : (y, x) ⟂ᵢ[𝕡] z := IndepJoint.of.Indep.Indep_Joint hy hx
  have hcomp : (x, y) = Prod.swap ∘ (y, x) := by
    funext ω; rfl
  rw [hcomp]
  exact h.comp measurable_swap measurable_id


-- created on 2026-09-19
