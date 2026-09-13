import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import sympy.stats.joint_rv
import sympy.Basic
open MeasureTheory


/--
| attributes | lemma |
| :---: | :---: |
| main | Random.MeasurableJointRandomSymbol.is.Measurable.Measurable |
| comm | Random.Measurable.Measurable.is.MeasurableJointRandomSymbol |
| mp | Random.Measurable.Measurable.of.MeasurableJointRandomSymbol |
| mpr | Random.MeasurableJointRandomSymbol.of.Measurable.Measurable |
-/
@[main, comm, mp, mpr]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  {x : Ω → α} {y : Ω → β} :
-- imply
  Measurable (x ⊗ y) ↔ Measurable x ∧ Measurable y := by
-- proof
  refine' ⟨fun hxy ↦ ⟨measurable_fst.comp hxy, measurable_snd.comp hxy⟩, _⟩
  rintro ⟨hx, hy⟩
  exact hx.prodMk hy


-- created on 2026-09-13
