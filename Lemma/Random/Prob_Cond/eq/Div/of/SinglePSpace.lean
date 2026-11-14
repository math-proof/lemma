import Lemma.Random.EqProb
open MeasureTheory Measure Random


/--
Over countable discrete state spaces with counting reference measures, the conditional probability
is the ratio of the measures of the events:
`ℙ(x = «\sf{x}» | y = «\sf{y}») = π {ω | x ω = «\sf{x}» ∧ y ω = «\sf{y}»} / π {ω | y ω = «\sf{y}»}`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [CountableMeasure α] [CountableMeasure β]
  [Countable α] [Countable β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β}
-- given
  (hP : SinglePSpace π (x, y))
  («\sf{x}» : α)
  («\sf{y}» : β) :
-- imply
  ℙ[π](x = «\sf{x}» | y = «\sf{y}») =
    π (x ⁻¹' {«\sf{x}»} ∩ y ⁻¹' {«\sf{y}»}) / π (y ⁻¹' {«\sf{y}»}) := by
-- proof
  have := hP
  have hxy : AEMeasurable (x, y) π := PSpace.aemeasurable
  have hy : AEMeasurable y π := hxy.snd
  have h₁ : ℙ[π](x = «\sf{x}» ∧ y = «\sf{y}») =
      π (x ⁻¹' {«\sf{x}»} ∩ y ⁻¹' {«\sf{y}»}) := by
    rw [EqProb]
    congr 1
    ext ω
    simp [JointRandomSymbol, Prod.ext_iff]
  have h₂ : (π.map (fun ω ↦ ((x, y) ω).2)).rnDeriv ReferenceMeasure.measure «\sf{y}» =
      π (y ⁻¹' {«\sf{y}»}) := by
    rw [CountableMeasure.measure_eq_count (α := β), EqRnDeriv_Count]
    apply Measure.map_apply_of_aemeasurable hy (measurableSet_singleton «\sf{y}»)
  unfold Measure.condProb
  apply congrArg₂ _ h₁ h₂


-- created on 2026-10-02
-- updated on 2026-11-02
