import Mathlib.MeasureTheory.Measure.MeasureSpace
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  {π : Measure Ω} {x : Ω → α} [PSpace π x]
-- given
  (ω : Ω) :
-- imply
  ℙ[π](x) ω = ℙ[π](x = x ω) := by
-- proof
  rfl


-- created on 2026-09-20
