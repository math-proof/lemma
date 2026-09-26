import Mathlib.MeasureTheory.Measure.Count
import Lemma.Measure.EqRnDeriv_Count
import Lemma.Random.PSpace.of.Measure.eq.Count.Measurable
import sympy.stats.joint_rv
open MeasureTheory Measure Random


/--
If the point mass of `x = v` is nonzero, then every measurable slice
(viewed as a measurable function `g` of the value, e.g. a prefix slice) also
has nonzero point mass at the sliced value: `g ⁻¹' {g v}` contains the
atom `x ⁻¹' {v}`.

Python: Random.Ne_0.Slice.of.Ne_0.
-/
@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  [Countable α] [Countable β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  {π : Measure Ω}
  {x : Ω → α} {g : α → β}
  [PSpace π x]
-- given
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (hβ : ReferenceMeasure.measure (α := β) = Measure.count)
  (hx : Measurable x)
  (hg : Measurable g)
  (v : α)
  (h : ℙ[π](x = v) ≠ 0) :
-- imply
  have : PSpace π (g ∘ x) :=
    PSpace.of.Measure.eq.Count.Measurable (hg.comp hx) hβ
  Measure.prob π (g ∘ x) (g v) ≠ 0 := by
-- proof
  intro hPg
  let y : Ω → β := g ∘ x
  have hpre : x ⁻¹' {v} ⊆ y ⁻¹' {g v} := by
    intro ω hω
    simp only [y, Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    exact congrArg g hω
  have hmass_v :
      (π.map x).rnDeriv ReferenceMeasure.measure v = π (x ⁻¹' {v}) := by
    rw [hα, EqRnDeriv_Count (μ := π.map x) v,
      Measure.map_apply_of_aemeasurable hx.aemeasurable (measurableSet_singleton v)]
  have hmass_gv :
      (π.map y).rnDeriv ReferenceMeasure.measure (g v) =
        π (y ⁻¹' {g v}) := by
    rw [hβ, EqRnDeriv_Count (μ := π.map y) (g v),
      Measure.map_apply_of_aemeasurable (hg.comp hx).aemeasurable
        (measurableSet_singleton (g v))]
  have hxv : π (x ⁻¹' {v}) ≠ 0 := by
    simpa [Measure.prob, hmass_v] using h
  by_contra h0
  rw [Measure.prob, hmass_gv] at h0
  have hz : π (x ⁻¹' {v}) = 0 := measure_mono_null hpre h0
  exact hxv hz


-- created on 2026-09-26
