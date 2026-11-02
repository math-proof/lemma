import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Lemma.Random.PSpace_Joint_Joint.of.PSpace_Joint
import Lemma.Random.PSpace_JointJoint.is.PSpace_Joint_Joint
import Lemma.Measure.EqRnDeriv_Count
import Lemma.Measure.Count.eq.ProdCountS
open MeasureTheory Measure Function Random


@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure γ]
  [Countable α] [Countable γ]
  [MeasurableSingletonClass α] [MeasurableSingletonClass γ]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → γ}
-- given
  (hP : SinglePSpace π (x, y))
  (hα : ReferenceMeasure.measure (α := α) = Measure.count)
  (hγ : ReferenceMeasure.measure (α := γ) = Measure.count)
  («\sf{x}» : α)
  («\sf{y}» : γ) :
-- imply
  have hPxyy : SinglePSpace π (x, y, y) := Random.PSpace_Joint_Joint.of.PSpace_Joint hP hα hγ
  have : SinglePSpace π ((x, y), y) := PSpace_JointJoint.of.PSpace_Joint_Joint hPxyy
  ℙ[π](x = «\sf{x}» ∧ y = «\sf{y}» | y = «\sf{y}») = ℙ[π](x = «\sf{x}» | y = «\sf{y}») := by
-- proof
  intro _ hP_left
  have hxym : AEMeasurable (x, y) π := hP.aemeasurable
  have hym : AEMeasurable y π := (SinglePSpace.of.SinglePSpace.snd hP).aemeasurable
  have hxyym : AEMeasurable ((x, y), y) π :=
    hP_left.aemeasurable
  have href_γ : ReferenceMeasure.measure (α := γ) = (count : Measure γ) := hγ
  have href_xy : ReferenceMeasure.measure (α := α × γ) = (count : Measure (α × γ)) := by
    change (ReferenceMeasure.measure (α := α)).prod (ReferenceMeasure.measure (α := γ)) =
      (count : Measure (α × γ))
    rw [hα, hγ, ← Count.eq.ProdCountS]
  have href_xy_y : ReferenceMeasure.measure (α := (α × γ) × γ) =
      (count : Measure ((α × γ) × γ)) := by
    change ((ReferenceMeasure.measure (α := α)).prod (ReferenceMeasure.measure (α := γ))).prod
        (ReferenceMeasure.measure (α := γ)) =
      (count : Measure ((α × γ) × γ))
    rw [hα, hγ, ← Count.eq.ProdCountS (α := α) (β := γ), ← Count.eq.ProdCountS]
  have : IsProbabilityMeasure (π.map (x, y)) :=
    inferInstance
  have : IsProbabilityMeasure (π.map y) :=
    inferInstance
  have : IsProbabilityMeasure (π.map ((x, y), y)) :=
    inferInstance
  have hmass_xy :
      (π.map (x, y)).rnDeriv (count : Measure (α × γ)) («\sf{x}», «\sf{y}») =
        π.map (x, y) {(«\sf{x}», «\sf{y}»)} :=
    EqRnDeriv_Count _
  have hmass_y :
      (π.map y).rnDeriv (count : Measure γ) «\sf{y}» = π.map y {«\sf{y}»} :=
    EqRnDeriv_Count _
  have hmass_xy_y :
      (π.map ((x, y), y)).rnDeriv
          (count : Measure ((α × γ) × γ)) ((«\sf{x}», «\sf{y}»), «\sf{y}») =
        π.map ((x, y), y)
          {((«\sf{x}», «\sf{y}»), «\sf{y}»)} :=
    EqRnDeriv_Count _
  have hpre :
      ((x, y), y) ⁻¹'
          {((«\sf{x}», «\sf{y}»), «\sf{y}»)} =
        (x, y) ⁻¹' {(«\sf{x}», «\sf{y}»)} := by
    ext ω
    simp [JointRandomSymbol, Prod.mk.injEq]
  have hset :
      π.map ((x, y), y)
          {((«\sf{x}», «\sf{y}»), «\sf{y}»)} =
        π.map (x, y) {(«\sf{x}», «\sf{y}»)} := by
    rw [Measure.map_apply_of_aemeasurable hxyym (measurableSet_singleton _),
      Measure.map_apply_of_aemeasurable hxym (measurableSet_singleton _), hpre]
  dsimp only [Measure.condProb, Measure.prob]
  have hden_xy :
      π.map (fun ω ↦ ((x, y) ω).2) = π.map y := rfl
  have hden_xy_y :
      π.map (fun ω ↦ (((x, y), y) ω).2) = π.map y := rfl
  rw [hden_xy, hden_xy_y]
  simp only [href_xy_y, href_xy, href_γ, hmass_xy_y, hmass_xy, hmass_y, hset]


-- created on 2026-09-20
-- updated on 2026-11-02
