import Mathlib.MeasureTheory.Measure.Count
import Lemma.Measure.EqRnDeriv_Count
import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Random.PSpace.of.Measure.eq.Count.Measurable
import sympy.stats.joint_rv
open MeasureTheory Measure Random


/--
If a joint point mass `x = v ∧ y = w` is nonzero, then the point mass of any
joint measurable slices (`g` on the value of `x`, `k` on the value of `y`, e.g.
prefix slices) at `(g v, k w)` is nonzero: the sliced atom's preimage contains
the original atom's preimage.

Python: Random.Ne_0.of.Ne_0.joint_slice.
-/
@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  [ReferenceMeasure α'] [ReferenceMeasure β']
  [Countable α] [Countable β]
  [Countable α'] [Countable β']
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [MeasurableSingletonClass α'] [MeasurableSingletonClass β']
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
  {g : α → α'} {k : β → β'}
  [PSpace π (x, y)]
-- given
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (hβ : ReferenceMeasure.measure (α := β) = Measure.count)
  (hα' : ReferenceMeasure.measure (α := α') = Measure.count)
  (hβ' : ReferenceMeasure.measure (α := β') = Measure.count)
  (hx : Measurable x)
  (hy : Measurable y)
  (hg : Measurable g)
  (hk : Measurable k)
  (v : α)
  (w : β)
  (h : ℙ[π](x = v ∧ y = w) ≠ 0) :
-- imply
  have : ReferenceMeasure.measure (α := α × β) = Measure.count := by
    change (ReferenceMeasure.measure (α := α)).prod
        ReferenceMeasure.measure = Measure.count
    rw [hα, hβ, ← Count.eq.ProdCountS]
  have : ReferenceMeasure.measure (α := α' × β') = Measure.count := by
    change (ReferenceMeasure.measure (α := α')).prod
        ReferenceMeasure.measure = Measure.count
    rw [hα', hβ', ← Count.eq.ProdCountS]
  have : PSpace π (g ∘ x, k ∘ y) :=
    PSpace.of.Measure.eq.Count.Measurable
      ((hg.comp hx).prodMk (hk.comp hy)) ‹_›
  Measure.prob π (g ∘ x, k ∘ y) (g v, k w) ≠ 0 := by
-- proof
  intro href href' _
  let z : Ω → α' × β' := JointRandomSymbol (g ∘ x) (k ∘ y)
  have hxym : AEMeasurable (JointRandomSymbol x y) π :=
    (hx.prodMk hy).aemeasurable
  have hzm : AEMeasurable z π :=
    ((hg.comp hx).prodMk (hk.comp hy)).aemeasurable
  have hpre : (x, y) ⁻¹' {(v, w)} ⊆ z ⁻¹' {(g v, k w)} := by
    intro ω hω
    simp only [z, JointRandomSymbol, Set.mem_preimage, Set.mem_singleton_iff,
      Prod.mk.injEq] at hω ⊢
    exact ⟨congrArg g hω.1, congrArg k hω.2⟩
  have hmass_vw :
      (π.map (x, y)).rnDeriv ReferenceMeasure.measure (v, w) =
        π ((x, y) ⁻¹' {(v, w)}) := by
    rw [href, EqRnDeriv_Count (μ := π.map (x, y)) (v, w),
      Measure.map_apply_of_aemeasurable hxym (measurableSet_singleton (v, w))]
  have hmass_gvkw :
      (π.map z).rnDeriv ReferenceMeasure.measure (g v, k w) =
        π (z ⁻¹' {(g v, k w)}) := by
    rw [href', EqRnDeriv_Count (μ := π.map z) (g v, k w),
      Measure.map_apply_of_aemeasurable hzm
        (measurableSet_singleton (g v, k w))]
  have hne : π ((x, y) ⁻¹' {(v, w)}) ≠ 0 := by
    simpa [Measure.prob, hmass_vw] using h
  by_contra h0
  rw [Measure.prob, hmass_gvkw] at h0
  exact hne (measure_mono_null hpre h0)


-- created on 2026-09-26
