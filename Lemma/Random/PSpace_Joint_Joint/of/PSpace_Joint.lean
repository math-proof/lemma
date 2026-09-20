import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.WithDensity
import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
import sympy.stats.joint_rv
open MeasureTheory Function Random
open scoped Classical

/-!
Under counting reference measures, a joint density for `(x, y)` yields a joint density
for the diagonal embedding `(x, y, y)`.
-/

private lemma count_prod_singleton
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (a : α) (b : β) :
    ((Measure.count : Measure α).prod (Measure.count : Measure β)) {(a, b)} = 1 := by
  have : ({(a, b)} : Set (α × β)) = ({a} : Set α) ×ˢ ({b} : Set β) := by
    ext ⟨x, y⟩; simp [Prod.mk.injEq]
  rw [this, Measure.prod_prod, Measure.count_singleton, Measure.count_singleton, mul_one]

private lemma count_eq_prod
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    (Measure.count : Measure (α × β)) = (Measure.count : Measure α).prod (Measure.count : Measure β) := by
  refine Measure.ext_iff_singleton.mpr fun z => ?_
  rw [Measure.count_singleton, count_prod_singleton]

/-- Joint diagonal embedding `(a, b) ↦ (a, (b, b))`. -/
private def jointDiag (α γ : Type*) : α × γ → α × γ × γ :=
  fun p => (p.1, p.2, p.2)

private lemma measurable_jointDiag
    {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ] :
    Measurable (jointDiag α γ) :=
  measurable_fst.prodMk (measurable_snd.prodMk measurable_snd)

/-- Preimage of a singleton under `jointDiag`. -/
private lemma jointDiag_preimage_singleton
    {α γ : Type*} (z : α × γ × γ) :
    jointDiag α γ ⁻¹' {z} =
      if z.2.1 = z.2.2 then {(z.1, z.2.1)} else (∅ : Set (α × γ)) := by
  split_ifs with h
  · ext w
    simp only [jointDiag, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hw
      have hw1 : w.1 = z.1 := congrArg Prod.fst hw
      have hw2 : w.2 = z.2.1 := by
        have := congrArg (fun t : α × γ × γ => t.2.1) hw
        simpa using this
      exact Prod.ext hw1 hw2
    · intro hw
      have hw' : w = (z.1, z.2.1) := hw
      subst hw'
      apply Prod.ext
      · rfl
      · exact Prod.ext rfl h
  · ext w
    simp only [jointDiag, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false]
    intro hw
    have hw2 : w.2 = z.2.1 := by
      have := congrArg (fun t : α × γ × γ => t.2.1) hw
      simpa using this
    have hw3 : w.2 = z.2.2 := by
      have := congrArg (fun t : α × γ × γ => t.2.2) hw
      simpa using this
    exact h (hw2.symm.trans hw3)


@[main]
private lemma main
  {Ω α γ : Type*}
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure γ]
  [Countable α] [Countable γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass γ]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → γ}
-- given
  (hP : PSpace π (x, y))
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (hγ : ReferenceMeasure.measure (α := γ) = Measure.count) :
-- imply
  PSpace π (x, y, y) := by
-- proof
  change PSpace π (JointRandomSymbol x (JointRandomSymbol y y))
  have hxym : AEMeasurable (JointRandomSymbol x y) π := by
    simpa [JointRandomSymbol] using hP.aemeasurable
  have hcomp :
      JointRandomSymbol x (JointRandomSymbol y y) =
        jointDiag α γ ∘ JointRandomSymbol x y := rfl
  have hxyym : AEMeasurable (JointRandomSymbol x (JointRandomSymbol y y)) π := by
    rw [hcomp]
    exact measurable_jointDiag.comp_aemeasurable hxym
  obtain ⟨p, D, hlaw⟩ := hP.exists_distribution
  have hp : Measurable p := D.measurable_density
  have href_xy : ReferenceMeasure.measure (α := α × γ) = (Measure.count : Measure (α × γ)) := by
    change (ReferenceMeasure.measure (α := α)).prod (ReferenceMeasure.measure (α := γ)) =
      (Measure.count : Measure (α × γ))
    rw [hα, hγ, ← count_eq_prod]
  have href_xyy : ReferenceMeasure.measure (α := α × γ × γ) =
      (Measure.count : Measure (α × γ × γ)) := by
    change (ReferenceMeasure.measure (α := α)).prod
        ((ReferenceMeasure.measure (α := γ)).prod (ReferenceMeasure.measure (α := γ))) =
      (Measure.count : Measure (α × (γ × γ)))
    rw [hα, hγ, ← count_eq_prod (α := γ) (β := γ), ← count_eq_prod]
  have hlaw' :
      π.map (JointRandomSymbol x y) = (Measure.count : Measure (α × γ)).withDensity p := by
    have h : π.map (JointRandomSymbol x y) =
        (ReferenceMeasure.measure (α := α × γ)).withDensity p := by
      simpa [Distributed, JointRandomSymbol] using hlaw
    rw [h, href_xy]
  let ρ : α × γ × γ → ENNReal := fun z => if z.2.1 = z.2.2 then p (z.1, z.2.1) else 0
  have hρ : Measurable ρ := by
    classical
    refine Measurable.ite ?_ (hp.comp (measurable_fst.prodMk measurable_snd.fst)) measurable_const
    exact measurableSet_eq_fun measurable_snd.fst measurable_snd.snd
  have hmap :
      π.map (JointRandomSymbol x (JointRandomSymbol y y)) =
        (π.map (JointRandomSymbol x y)).map (jointDiag α γ) := by
    rw [hcomp]
    exact (AEMeasurable.map_map_of_aemeasurable
      measurable_jointDiag.aemeasurable hxym).symm
  have htarget :
      π.map (JointRandomSymbol x (JointRandomSymbol y y)) =
        (Measure.count : Measure (α × γ × γ)).withDensity ρ := by
    rw [hmap, hlaw']
    refine Measure.ext_iff_singleton.mpr fun z => ?_
    have happly :=
      Measure.map_apply (μ := (Measure.count : Measure (α × γ)).withDensity p)
        measurable_jointDiag (measurableSet_singleton z)
    rw [happly, withDensity_apply _ (measurableSet_singleton z), lintegral_singleton,
      Measure.count_singleton, mul_one]
    rw [jointDiag_preimage_singleton]
    split_ifs with hdiag
    · have hz : ((Measure.count : Measure (α × γ)).withDensity p) {(z.1, z.2.1)} =
          p (z.1, z.2.1) := by
        rw [withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
          Measure.count_singleton, mul_one]
      rw [hz]; simp [ρ, hdiag]
    · rw [measure_empty]; simp [ρ, hdiag]
  refine {
    toIsProbabilityMeasure := inferInstance
    aemeasurable := hxyym
    exists_distribution := ⟨ρ, ⟨hρ⟩, ?_⟩
  }
  show π.map (JointRandomSymbol x (JointRandomSymbol y y)) =
    ReferenceMeasure.measure.withDensity ρ
  rw [htarget, href_xyy]
