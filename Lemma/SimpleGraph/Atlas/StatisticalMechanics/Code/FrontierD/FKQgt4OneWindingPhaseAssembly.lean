import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4OneWindingPhaseAssembly
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FrontierD


/--
[fkQgt4CriticalFreeTheta_eq_zero_of_exactDiagonalRatePos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OneWindingPhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeTheta_eq_zero_of_exactDiagonalRatePos_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hpos : 0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq) :
-- imply
  FK.fkThetaFree 2 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) (q := q) = 0 := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeTheta_eq_zero_of_exactDiagonalRatePos hq hpos

/--
[fkQgt4_firstOrder_of_gapRate_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OneWindingPhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_firstOrder_of_gapRate_le_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hone : fkQgt4SixVertexGapRate q <= fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) :
-- imply
  FK.IsFirstOrderTransition 2 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_firstOrder_of_gapRate_le hq hone

/--
[fkQgt4_firstOrder_of_horizontalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OneWindingPhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_firstOrder_of_horizontalCrossing_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (hcross : forall scale k : Nat, 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, 1 / (2 * (1 + q)) <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (3 * (scale : Int)) 0 scale)) :
-- imply
  FK.IsFirstOrderTransition 2 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_firstOrder_of_horizontalCrossing hq hcross

/--
[fkQgt4_firstOrder_of_evenHorizontalCrossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OneWindingPhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_firstOrder_of_evenHorizontalCrossingFloor_eq
  {q crossingFloor : Real}
-- given
  (hq : 4 < q)
  (hcrossingFloor : 0 < crossingFloor)
  (hcross : forall scale k : Nat, Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, crossingFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (3 * (scale : Int)) 0 scale)) :
-- imply
  FK.IsFirstOrderTransition 2 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_firstOrder_of_evenHorizontalCrossingFloor hq hcrossingFloor hcross

/--
[fkQgt4_critical_potts_phases_of_gapRate_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OneWindingPhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_critical_potts_phases_of_gapRate_le_eq
  {q : Nat}
  [NeZero q]
  {J : Real}
-- given
  (hq : 4 < q)
  (hJ : 0 < J)
  (hone : fkQgt4SixVertexGapRate q <= fkQgt4CriticalFreeExactDiagonalRateLimit (by exact_mod_cast hq : (4 : Real) < q) / 2) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)) (phiFree : Nat -> Nat) (phiWired : Fin q -> Nat -> Nat), Tendsto (fun n => freePottsFiniteMeasure 2 (phiFree n) q (pottsSelfDualInverseTemperature q J) J) atTop (nhds muFree) ∧ (∀ b, StrictMono (phiWired b) ∧ Tendsto (fun n => wiredPottsFiniteMeasure 2 (phiWired b n) q b (pottsSelfDualInverseTemperature q J) J) atTop (nhds (muWired b))) ∧ (∀ b, muFree ≠ muWired b) ∧ ∀ b c, b ≠ c -> muWired b ≠ muWired c := by
-- proof
  apply StatMech.FrontierD.fkQgt4_critical_potts_phases_of_gapRate_le q hq J hJ hone

/--
[fkQgt4_critical_potts_phases_of_horizontalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OneWindingPhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_critical_potts_phases_of_horizontalCrossing_eq
  {q : Nat}
  [NeZero q]
  {J : Real}
-- given
  (hq : 4 < q)
  (hJ : 0 < J)
  (hcross : forall scale k : Nat, 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, 1 / (2 * (1 + (q : Real))) <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (3 * (scale : Int)) 0 scale)) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)) (phiFree : Nat -> Nat) (phiWired : Fin q -> Nat -> Nat), Tendsto (fun n => freePottsFiniteMeasure 2 (phiFree n) q (pottsSelfDualInverseTemperature q J) J) atTop (nhds muFree) ∧ (∀ b, StrictMono (phiWired b) ∧ Tendsto (fun n => wiredPottsFiniteMeasure 2 (phiWired b n) q b (pottsSelfDualInverseTemperature q J) J) atTop (nhds (muWired b))) ∧ (∀ b, muFree ≠ muWired b) ∧ ∀ b c, b ≠ c -> muWired b ≠ muWired c := by
-- proof
  apply StatMech.FrontierD.fkQgt4_critical_potts_phases_of_horizontalCrossing q hq J hJ hcross

/--
[fkQgt4_critical_ergodic_potts_phases_of_horizontalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OneWindingPhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_critical_ergodic_potts_phases_of_horizontalCrossing_eq
  {q : Nat}
  [NeZero q]
-- given
  (hq : 4 < q)
  (hcross : forall scale k : Nat, 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, 1 / (2 * (1 + (q : Real))) <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (3 * (scale : Int)) 0 scale)) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)), IsErgodicFor (pottsSpinShift (d := 2) (q := q)) (muFree : Measure _) ∧ (forall b, IsErgodicFor (pottsSpinShift (d := 2) (q := q)) (muWired b : Measure _)) ∧ (forall b, muFree ≠ muWired b) ∧ forall b c, b ≠ c -> muWired b ≠ muWired c := by
-- proof
  apply StatMech.FrontierD.fkQgt4_critical_ergodic_potts_phases_of_horizontalCrossing q hq hcross

/--
[fkQgt4_critical_ergodic_potts_phases_of_evenHorizontalCrossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4OneWindingPhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_critical_ergodic_potts_phases_of_evenHorizontalCrossingFloor_eq
  {q : Nat}
  [NeZero q]
  {crossingFloor : Real}
-- given
  (hq : 4 < q)
  (hcrossingFloor : 0 < crossingFloor)
  (hcross : forall scale k : Nat, Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, crossingFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (3 * (scale : Int)) 0 scale)) :
-- imply
  ∃ (muFree : ProbabilityMeasure (PottsConfig 2 q)) (muWired : Fin q -> ProbabilityMeasure (PottsConfig 2 q)), IsErgodicFor (pottsSpinShift (d := 2) (q := q)) (muFree : Measure _) ∧ (forall b, IsErgodicFor (pottsSpinShift (d := 2) (q := q)) (muWired b : Measure _)) ∧ (forall b, muFree ≠ muWired b) ∧ forall b c, b ≠ c -> muWired b ≠ muWired c := by
-- proof
  apply StatMech.FrontierD.fkQgt4_critical_ergodic_potts_phases_of_evenHorizontalCrossingFloor q hq hcrossingFloor hcross


-- created on 2026-10-23
