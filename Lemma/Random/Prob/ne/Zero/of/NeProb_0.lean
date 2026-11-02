import Mathlib.MeasureTheory.Measure.Count
import Lemma.Measure.EqRnDeriv_Count
import Instance.Probability.SinglePSpaceMeasurable
open MeasureTheory Measure Random


/--
If the point mass of `x = «\sf{x}»` is nonzero and `g` is measurable, then the
point mass of `g ∘ x = g «\sf{x}»` is nonzero. The atom
`x ⁻¹' {«\sf{x}»}` is contained in `(g ∘ x) ⁻¹' {g «\sf{x}»}`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [CountableMeasure α] [CountableMeasure β]
  [Countable α] [Countable β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {x : Ω → α}
  {g : α → β}
-- given
  («\sf{x}» : α)
  (hg : Measurable g)
  [hx : Fact (Measurable x)]
  (h : ℙ[π](x = «\sf{x}») ≠ 0) :
-- imply
  have : SinglePSpace π (g ∘ x) :=
    SinglePSpace.of.Measurable (hg.comp hx.out)
  Measure.prob π (g ∘ x) (g «\sf{x}») ≠ 0 := by
-- proof
  intro hPg
  let y : Ω → β := g ∘ x
  have hpre : x ⁻¹' {«\sf{x}»} ⊆ y ⁻¹' {g «\sf{x}»} := by
    intro ω hω
    simp only [y, Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    apply congrArg g hω
  have hmass_v :
    (π.map x).rnDeriv ReferenceMeasure.measure «\sf{x}» = π (x ⁻¹' {«\sf{x}»}) := by
    rw [CountableMeasure.measure_eq_count, EqRnDeriv_Count (μ := π.map x) «\sf{x}»,
      Measure.map_apply_of_aemeasurable hx.out.aemeasurable (measurableSet_singleton «\sf{x}»)]
  have hmass_gv :
    (π.map y).rnDeriv ReferenceMeasure.measure (g «\sf{x}») =
      π (y ⁻¹' {g «\sf{x}»}) := by
    rw [CountableMeasure.measure_eq_count (α := β), EqRnDeriv_Count (μ := π.map y) (g «\sf{x}»),
      Measure.map_apply_of_aemeasurable (hg.comp hx.out).aemeasurable
        (measurableSet_singleton (g «\sf{x}»))]
  have hxv : π (x ⁻¹' {«\sf{x}»}) ≠ 0 := by
    rwa [Measure.prob, hmass_v] at h
  by_contra h0
  rw [Measure.prob, hmass_gv] at h0
  apply hxv
  apply measure_mono_null hpre h0


-- created on 2026-10-23
-- updated on 2026-11-02
