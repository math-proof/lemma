import Mathlib.Probability.Independence.Basic
import sympy.stats.joint_rv
import Lemma.Random.IndepJoint.of.Indep.Indep_Joint
open ProbabilityTheory MeasureTheory Random


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
  [PSpace π x] [PSpace π y] [PSpace π z]
-- given
  (hx : x ⟂ᵢ[π] (y, z))
  (hy : y ⟂ᵢ[π] z) :
-- imply
  (x, y) ⟂ᵢ[π] z := by
-- proof
  have h : (y, x) ⟂ᵢ[π] z := IndepJoint.of.Indep.Indep_Joint hy hx
  have hcomp : (x, y) = Prod.swap ∘ (y, x) := by
    funext ω; rfl
  rw [hcomp]
  exact h.comp measurable_swap measurable_id


-- created on 2026-09-19
