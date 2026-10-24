import Lemma.Random.EqProb
open MeasureTheory Measure Random


/--
Over countable discrete state spaces with counting reference measures, the conditional probability
is the ratio of the measures of the events:
`ℙ(x = «x.bvar» | y = «y.bvar») = π {ω | x ω = «x.bvar» ∧ y ω = «y.bvar»} / π {ω | y ω = «y.bvar»}`.
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
  («x.bvar» : α)
  («y.bvar» : β) :
-- imply
  ℙ[π](x = «x.bvar» | y = «y.bvar») =
    π (x ⁻¹' {«x.bvar»} ∩ y ⁻¹' {«y.bvar»}) / π (y ⁻¹' {«y.bvar»}) := by
-- proof
  have := hP
  have hxy : AEMeasurable (x, y) π := PSpace.aemeasurable
  have hy : AEMeasurable y π := hxy.snd
  have h₁ : ℙ[π](x = «x.bvar» ∧ y = «y.bvar») =
      π (x ⁻¹' {«x.bvar»} ∩ y ⁻¹' {«y.bvar»}) := by
    rw [EqProb]
    congr 1
    ext ω
    simp [JointRandomSymbol, Prod.ext_iff]
  have h₂ : (π.map (fun ω ↦ ((x, y) ω).2)).rnDeriv ReferenceMeasure.measure «y.bvar» =
      π (y ⁻¹' {«y.bvar»}) := by
    rw [CountableMeasure.measure_eq_count (α := β), EqRnDeriv_Count]
    apply Measure.map_apply_of_aemeasurable hy (measurableSet_singleton «y.bvar»)
  unfold Measure.condProb
  apply congrArg₂ _ h₁ h₂


-- created on 2026-10-02
-- updated on 2026-10-23
