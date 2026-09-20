import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Lemma.Random.PSpace.PSpace.of.PSpace_Joint
import Lemma.Random.PSpace_Joint_Joint.of.PSpace_Joint
import Lemma.Measure.EqRnDeriv_Count
import Lemma.Measure.Count.eq.ProdCountS
import sympy.stats.joint_rv
open MeasureTheory Measure Function Random


@[main]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure γ]
  [Countable α] [Countable γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass γ]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → γ}
-- given
  (hP : PSpace π (x, y))
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (hγ : ReferenceMeasure.measure (α := γ) = Measure.count)
  («x.bvar» : α)
  («y.bvar» : γ) :
-- imply
  have : PSpace π (x, y, y) := Random.PSpace_Joint_Joint.of.PSpace_Joint hP hα hγ
  ℙ[π](x = «x.bvar» | y = «y.bvar» ∧ y = «y.bvar») = ℙ[π](x = «x.bvar» | y = «y.bvar») := by
-- proof
  intro hPyy
  have hxym : AEMeasurable (JointRandomSymbol x y) π := hP.aemeasurable
  have hym : AEMeasurable y π := (PSpace.of.PSpace_Joint.snd hP).aemeasurable
  have hyym : AEMeasurable (JointRandomSymbol y y) π :=
    (measurable_id.prodMk measurable_id).comp_aemeasurable hym
  have hxyym : AEMeasurable (JointRandomSymbol x (JointRandomSymbol y y)) π :=
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
  have : IsProbabilityMeasure (π.map (JointRandomSymbol x y)) :=
    Measure.isProbabilityMeasure_map hxym
  have : IsProbabilityMeasure (π.map y) :=
    Measure.isProbabilityMeasure_map hym
  have : IsProbabilityMeasure (π.map (JointRandomSymbol y y)) :=
    Measure.isProbabilityMeasure_map hyym
  have : IsProbabilityMeasure (π.map (JointRandomSymbol x (JointRandomSymbol y y))) :=
    Measure.isProbabilityMeasure_map hxyym
  have hmass_xy :
      (π.map (JointRandomSymbol x y)).rnDeriv (count : Measure (α × γ)) («x.bvar», «y.bvar») =
        π.map (JointRandomSymbol x y) {(«x.bvar», «y.bvar»)} :=
    EqRnDeriv_Count _
  have hmass_y :
      (π.map y).rnDeriv (count : Measure γ) «y.bvar» = π.map y {«y.bvar»} :=
    EqRnDeriv_Count _
  have hmass_yy :
      (π.map (JointRandomSymbol y y)).rnDeriv (count : Measure (γ × γ)) («y.bvar», «y.bvar») =
        π.map (JointRandomSymbol y y) {(«y.bvar», «y.bvar»)} :=
    EqRnDeriv_Count _
  have hmass_xyy :
      (π.map (JointRandomSymbol x (JointRandomSymbol y y))).rnDeriv
          (count : Measure (α × γ × γ)) («x.bvar», «y.bvar», «y.bvar») =
        π.map (JointRandomSymbol x (JointRandomSymbol y y)) {(«x.bvar», «y.bvar», «y.bvar»)} :=
    EqRnDeriv_Count _
  have hpre_xyy :
      JointRandomSymbol x (JointRandomSymbol y y) ⁻¹' {(«x.bvar», «y.bvar», «y.bvar»)} =
        JointRandomSymbol x y ⁻¹' {(«x.bvar», «y.bvar»)} := by
    ext ω
    simp [JointRandomSymbol, Prod.mk.injEq]
  have hpre_yy :
      JointRandomSymbol y y ⁻¹' {(«y.bvar», «y.bvar»)} = y ⁻¹' {«y.bvar»} := by
    ext ω
    simp [JointRandomSymbol, Prod.mk.injEq]
  have hset_xyy :
      π.map (JointRandomSymbol x (JointRandomSymbol y y)) {(«x.bvar», «y.bvar», «y.bvar»)} =
        π.map (JointRandomSymbol x y) {(«x.bvar», «y.bvar»)} := by
    rw [Measure.map_apply_of_aemeasurable hxyym (measurableSet_singleton _),
      Measure.map_apply_of_aemeasurable hxym (measurableSet_singleton _), hpre_xyy]
  have hset_yy :
      π.map (JointRandomSymbol y y) {(«y.bvar», «y.bvar»)} = π.map y {«y.bvar»} := by
    rw [Measure.map_apply_of_aemeasurable hyym (measurableSet_singleton _),
      Measure.map_apply_of_aemeasurable hym (measurableSet_singleton _), hpre_yy]
  dsimp only [Measure.condProb, Measure.prob]
  have hden_y :
      π.map (fun ω ↦ (JointRandomSymbol x y ω).2) = π.map y := rfl
  have hden_yy :
      π.map (fun ω ↦ (JointRandomSymbol x (JointRandomSymbol y y) ω).2) =
        π.map (JointRandomSymbol y y) := rfl
  rw [hden_y, hden_yy]
  simp only [href_xyy, href_yy, href_xy, href_γ, hmass_xyy, hmass_yy, hmass_xy, hmass_y,
    hset_xyy, hset_yy]


-- created on 2026-09-20
