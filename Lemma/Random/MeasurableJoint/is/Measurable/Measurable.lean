import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Syntax.Probability.JointRv.Part6
import Initialize.Tactic.Attr.Basic
open MeasureTheory


/--
| attributes | lemma |
| :---: | :---: |
| path | Random.MeasurableJoint.is.Measurable.Measurable |
| comm | Random.Measurable.Measurable.is.MeasurableJoint |
| mp | Random.Measurable.Measurable.of.MeasurableJoint |
| mpr | Random.MeasurableJoint.of.Measurable.Measurable |
-/
@[path, comm, mp, mpr]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  {x : Ω → α} {y : Ω → β} :
-- imply
  Measurable (x, y) ↔ Measurable x ∧ Measurable y := by
-- proof
  refine' ⟨fun hxy ↦ ⟨measurable_fst.comp hxy, measurable_snd.comp hxy⟩, _⟩
  rintro ⟨hx, hy⟩
  exact hx.prodMk hy


-- created on 2026-09-13
