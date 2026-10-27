import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorMeasureClosure.Part2
open Filter MeasureTheory Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[measure_eq_zero_of_disjoint_measureReal_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorMeasureClosure.lean)
-/
@[path]
private lemma measure_eq_zero_of_disjoint_measureReal_tendsto_one_eq
  [MeasurableSpace X]
  {mu : Measure X}
  [IsProbabilityMeasure mu]
  {A : Nat → Set X}
  {B : Set X}
-- given
  (hB : MeasurableSet B)
  (hdisjoint : ∀ n, Disjoint (A n) B)
  (hA : Tendsto (fun n => mu.real (A n)) atTop (nhds 1)) :
-- imply
  mu B = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.measure_eq_zero_of_disjoint_measureReal_tendsto_one mu A B hB hdisjoint hA

/--
[dual_boundaryBand_measure_eq_zero_of_finiteDeepConnector_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorMeasureClosure.lean)
-/
@[path]
private lemma dual_boundaryBand_measure_eq_zero_of_finiteDeepConnector_tendsto_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {rPrimal Rdeep cArm dArm : Nat → Real}
  {width : Nat → Nat}
  {L U : Nat → Finset V}
  {rDual cBand dBand : Real}
-- given
  (hdeep : Tendsto (fun n => mu.real (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent (rPrimal n) (Rdeep n) (cArm n) (dArm n) (width n) (L n) (U n))) atTop (nhds 1))
  (hdisjoint : ∀ n, Disjoint (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent (rPrimal n) (Rdeep n) (cArm n) (dArm n) (width n) (L n) (U n)) ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster rDual cBand dBand)) :
-- imply
  D.dualMeasure mu (D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster rDual cBand dBand) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dual_boundaryBand_measure_eq_zero_of_finiteDeepConnector_tendsto_one D mu rPrimal Rdeep cArm dArm width L U rDual cBand dBand hdeep hdisjoint

/--
[complementaryDual_rightHalfPlane_measure_eq_zero_of_finiteDeepConnector_schedules](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorMeasureClosure.lean)
-/
@[path]
private lemma complementaryDual_rightHalfPlane_measure_eq_zero_of_finiteDeepConnector_schedules_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {rDual : Real}
-- given
  (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
  (hdualUnique : D.dualMeasure mu {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hschedule : ∀ band : Nat, D.FiniteDeepConnectorBandSchedule mu rDual band) :
-- imply
  D.dualMeasure mu (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.complementaryDual_rightHalfPlane_measure_eq_zero_of_finiteDeepConnector_schedules D mu hdualErgodic hdualUnique rDual hschedule


-- created on 2026-10-23
