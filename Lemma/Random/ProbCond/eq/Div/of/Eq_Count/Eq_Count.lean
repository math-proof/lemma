import Lemma.Measure.EqRnDeriv_Count
import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Random.Prob.eq.Measure.of.Eq_Count
import sympy.stats.joint_rv
open MeasureTheory Measure Random


/--
Over countable discrete state spaces with counting reference measures, the conditional probability
is the ratio of the measures of the events:
`ℙ(x = u | y = v) = π {ω | x ω = u ∧ y ω = v} / π {ω | y ω = v}`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β]
  [Countable α] [Countable β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
  [SinglePSpace π (x, y)]
-- given
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (hβ : ReferenceMeasure.measure (α := β) = Measure.count)
  (u : α)
  (v : β) :
-- imply
  ℙ[π](x = u | y = v) = π (x ⁻¹' {u} ∩ y ⁻¹' {v}) / π (y ⁻¹' {v}) := by
-- proof
  have hαβ : ReferenceMeasure.measure (α := α × β) = Measure.count := by
    change (ReferenceMeasure.measure (α := α)).prod ReferenceMeasure.measure = Measure.count
    rw [hα, hβ, ← Count.eq.ProdCountS]
  have hxy : AEMeasurable (x, y) π := PSpace.aemeasurable
  have hy : AEMeasurable y π := hxy.snd
  have h₁ : ℙ[π](x = u ∧ y = v) = π (x ⁻¹' {u} ∩ y ⁻¹' {v}) := by
    rw [Prob.eq.Measure.of.Eq_Count hαβ]
    congr 1
    ext ω
    simp [JointRandomSymbol, Prod.ext_iff]
  have h₂ : (π.map (fun ω ↦ ((x, y) ω).2)).rnDeriv ReferenceMeasure.measure v = π (y ⁻¹' {v}) := by
    rw [hβ, EqRnDeriv_Count]
    exact Measure.map_apply_of_aemeasurable hy (measurableSet_singleton v)
  unfold Measure.condProb
  exact congrArg₂ _ h₁ h₂


-- created on 2026-10-02