import Mathlib.MeasureTheory.Measure.Count
import Lemma.Measure.EqRnDeriv_Count
import Lemma.Random.SinglePSpace.of.EqMeasureCount.Measurable
import sympy.stats.joint_rv
open MeasureTheory Measure Random


/--
If the point mass of `x = «x.bvar»` is nonzero and `g` is measurable, then the
point mass of `g ∘ x = g «x.bvar»` is nonzero. The atom
`x ⁻¹' {«x.bvar»}` is contained in `(g ∘ x) ⁻¹' {g «x.bvar»}`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [CountableMeasure α] [CountableMeasure β]
  [Countable α] [Countable β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  {π : Measure Ω} {x : Ω → α} [SinglePSpace π x]
  {g : α → β}
-- given
  («x.bvar» : α)
  (hx : Measurable x)
  (hg : Measurable g)
  (h : ℙ[π](x = «x.bvar») ≠ 0) :
-- imply
  have : SinglePSpace π (g ∘ x) :=
    SinglePSpace.of.EqMeasureCount.Measurable (hg.comp hx)
      (CountableMeasure.measure_eq_count (α := β))
  Measure.prob π (g ∘ x) (g «x.bvar») ≠ 0 := by
-- proof
  intro hPg
  let y : Ω → β := g ∘ x
  have hpre : x ⁻¹' {«x.bvar»} ⊆ y ⁻¹' {g «x.bvar»} := by
    intro ω hω
    simp only [y, Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    exact congrArg g hω
  have hmass_v :
    (π.map x).rnDeriv ReferenceMeasure.measure «x.bvar» = π (x ⁻¹' {«x.bvar»}) := by
    rw [CountableMeasure.measure_eq_count, EqRnDeriv_Count (μ := π.map x) «x.bvar»,
      Measure.map_apply_of_aemeasurable hx.aemeasurable (measurableSet_singleton «x.bvar»)]
  have hmass_gv :
    (π.map y).rnDeriv ReferenceMeasure.measure (g «x.bvar») =
      π (y ⁻¹' {g «x.bvar»}) := by
    rw [CountableMeasure.measure_eq_count (α := β), EqRnDeriv_Count (μ := π.map y) (g «x.bvar»),
      Measure.map_apply_of_aemeasurable (hg.comp hx).aemeasurable
        (measurableSet_singleton (g «x.bvar»))]
  have hxv : π (x ⁻¹' {«x.bvar»}) ≠ 0 := by
    rwa [Measure.prob, hmass_v] at h
  by_contra h0
  rw [Measure.prob, hmass_gv] at h0
  exact hxv (measure_mono_null hpre h0)


-- created on 2026-10-23
