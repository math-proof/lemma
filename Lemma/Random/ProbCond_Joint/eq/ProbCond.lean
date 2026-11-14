import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Lemma.Random.PSpace_Joint_Joint.of.PSpace_Joint
import Lemma.Measure.EqRnDeriv_Count
import Lemma.Measure.Count.eq.ProdCountS
open MeasureTheory Measure Function Random


@[path]
private lemma main
  [MeasurableSpace Ω]
  [μ : ReferenceMeasure α] [ξ : ReferenceMeasure γ]
  [Countable α] [Countable γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass γ]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → γ}
-- given
  (hP : SinglePSpace π (x, y))
  (hα : μ.measure = Measure.count)
  (hγ : ξ.measure = Measure.count)
  («\sf{x}» : α)
  («\sf{y}» : γ) :
-- imply
  have : SinglePSpace π (x, y, y) := Random.PSpace_Joint_Joint.of.PSpace_Joint hP hα hγ
  ℙ[π](x = «\sf{x}» | y = «\sf{y}» ∧ y = «\sf{y}») = ℙ[π](x = «\sf{x}» | y = «\sf{y}») := by
-- proof
  intro hPyy
  have hxym : AEMeasurable (x, y) π := hP.aemeasurable
  have hym : AEMeasurable y π := (SinglePSpace.of.SinglePSpace.snd hP).aemeasurable
  have hyym : AEMeasurable (y, y) π :=
    (measurable_id.prodMk measurable_id).comp_aemeasurable hym
  have hxyym : AEMeasurable (x, (y, y)) π :=
    hPyy.aemeasurable
  have href_γ : ReferenceMeasure.measure (α := γ) = (count : Measure γ) := hγ
  have href_yy : ReferenceMeasure.measure (α := γ × γ) = (count : Measure (γ × γ)) := by
    change (ReferenceMeasure.measure (α := γ)).prod (ReferenceMeasure.measure (α := γ)) =
      (count : Measure (γ × γ))
    rw [hγ, ← Count.eq.ProdCountS]
  have href_xy : ReferenceMeasure.measure (α := α × γ) = (count : Measure (α × γ)) := by
    change (ReferenceMeasure.measure (α := α)).prod (ReferenceMeasure.measure (α := γ)) =
      (count : Measure (α × γ))
    rw [hα, hγ, ← Count.eq.ProdCountS]
  have href_xyy : ReferenceMeasure.measure (α := α × (γ × γ)) =
      (count : Measure (α × γ × γ)) := by
    change (ReferenceMeasure.measure (α := α)).prod
        ((ReferenceMeasure.measure (α := γ)).prod (ReferenceMeasure.measure (α := γ))) =
      (count : Measure (α × (γ × γ)))
    rw [hα, hγ, ← Count.eq.ProdCountS (α := γ) (β := γ), ← Count.eq.ProdCountS]
  have : IsProbabilityMeasure (π.map (x, y)) :=
    inferInstance
  have : IsProbabilityMeasure (π.map y) :=
    inferInstance
  have : IsProbabilityMeasure (π.map (y, y)) :=
    inferInstance
  have : IsProbabilityMeasure (π.map (x, (y, y))) :=
    inferInstance
  have hmass_xy :
      (π.map (x, y)).rnDeriv (count : Measure (α × γ)) («\sf{x}», «\sf{y}») =
        π.map (x, y) {(«\sf{x}», «\sf{y}»)} :=
    EqRnDeriv_Count _
  have hmass_y :
      (π.map y).rnDeriv (count : Measure γ) «\sf{y}» = π.map y {«\sf{y}»} :=
    EqRnDeriv_Count _
  have hmass_yy :
      (π.map (y, y)).rnDeriv (count : Measure (γ × γ)) («\sf{y}», «\sf{y}») =
        π.map (y, y) {(«\sf{y}», «\sf{y}»)} :=
    EqRnDeriv_Count _
  have hmass_xyy :
      (π.map (x, (y, y))).rnDeriv
          (count : Measure (α × γ × γ)) («\sf{x}», «\sf{y}», «\sf{y}») =
        π.map (x, (y, y)) {(«\sf{x}», «\sf{y}», «\sf{y}»)} :=
    EqRnDeriv_Count _
  have hpre_xyy :
      (x, (y, y)) ⁻¹' {(«\sf{x}», «\sf{y}», «\sf{y}»)} =
        (x, y) ⁻¹' {(«\sf{x}», «\sf{y}»)} := by
    ext ω
    simp [JointRandomSymbol, Prod.mk.injEq]
  have hpre_yy :
      (y, y) ⁻¹' {(«\sf{y}», «\sf{y}»)} = y ⁻¹' {«\sf{y}»} := by
    ext ω
    simp [JointRandomSymbol, Prod.mk.injEq]
  have hset_xyy :
      π.map (x, (y, y)) {(«\sf{x}», «\sf{y}», «\sf{y}»)} =
        π.map (x, y) {(«\sf{x}», «\sf{y}»)} := by
    rw [Measure.map_apply_of_aemeasurable hxyym (measurableSet_singleton _),
      Measure.map_apply_of_aemeasurable hxym (measurableSet_singleton _), hpre_xyy]
  have hset_yy :
      π.map (y, y) {(«\sf{y}», «\sf{y}»)} = π.map y {«\sf{y}»} := by
    rw [Measure.map_apply_of_aemeasurable hyym (measurableSet_singleton _),
      Measure.map_apply_of_aemeasurable hym (measurableSet_singleton _), hpre_yy]
  dsimp only [Measure.condProb, Measure.prob]
  have hden_y :
      π.map (fun ω ↦ ((x, y) ω).2) = π.map y := rfl
  have hden_yy :
      π.map (fun ω ↦ ((x, (y, y)) ω).2) =
        π.map (y, y) := rfl
  rw [hden_y, hden_yy]
  simp only [href_xyy, href_yy, href_xy, href_γ, hmass_xyy, hmass_yy, hmass_xy, hmass_y,
    hset_xyy, hset_yy]


-- created on 2026-09-20
-- updated on 2026-11-14
