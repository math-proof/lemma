import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexMinimalCyclePhysicalRepair
open StatMech StatMech.FrontierD StatMech.FrontierD.SixVertexTwoLayerUnitCycleRepair


/--
[target_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMinimalCyclePhysicalRepair.lean)
-/
@[path]
private lemma target_ice_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
  {repair : SixVertexTwoLayerUnitCycleRepair omega eta loopGrade}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule) :
-- imply
  repair.target.1.IceRule ∧ repair.target.2.IceRule := by
-- proof
  apply StatMech.FrontierD.SixVertexTwoLayerUnitCycleRepair.target_ice repair homega heta

/--
[first_upCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMinimalCyclePhysicalRepair.lean)
-/
@[path]
private lemma first_upCount_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
  {repair : SixVertexTwoLayerUnitCycleRepair omega eta loopGrade} :
-- imply
  (sixVertexUpCount (svTorusVerticalRows T repair.target.1 (svFinLast T.height_pos)) : Int) = (sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) : Int) + 1 := by
-- proof
  apply StatMech.FrontierD.SixVertexTwoLayerUnitCycleRepair.first_upCount repair

/--
[second_upCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMinimalCyclePhysicalRepair.lean)
-/
@[path]
private lemma second_upCount_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
  {repair : SixVertexTwoLayerUnitCycleRepair omega eta loopGrade} :
-- imply
  (sixVertexUpCount (svTorusVerticalRows T repair.target.2 (svFinLast T.height_pos)) : Int) = (sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) : Int) - 1 := by
-- proof
  apply StatMech.FrontierD.SixVertexTwoLayerUnitCycleRepair.second_upCount repair

/--
[target_twoCycleFine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMinimalCyclePhysicalRepair.lean)
-/
@[path]
private lemma target_twoCycleFine_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
  {repair : SixVertexTwoLayerUnitCycleRepair omega eta loopGrade} :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated (omega, eta) repair.target := by
-- proof
  apply StatMech.FrontierD.SixVertexTwoLayerUnitCycleRepair.target_twoCycleFine repair

/--
[SixVertexDisjointCapUnitRepair.toUnitCycleRepair_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMinimalCyclePhysicalRepair.lean)
-/
@[path]
private lemma toUnitCycleRepair_target_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
  {repair : SixVertexDisjointCapUnitRepair omega eta loopGrade} :
-- imply
  repair.toUnitCycleRepair.target = repair.target := by
-- proof
  apply StatMech.FrontierD.SixVertexDisjointCapUnitRepair.toUnitCycleRepair_target repair

/--
[canonicalPhysicalPairedBranches_of_unitCyclePairedRepairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMinimalCyclePhysicalRepair.lean)
-/
@[path]
private lemma canonicalPhysicalPairedBranches_of_unitCyclePairedRepairs_eq
-- given
  (hrepairs : SixVertexCanonicalPositiveEvenTraceUnitCyclePairedRepairs) :
-- imply
  SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches := by
-- proof
  apply StatMech.FrontierD.canonicalPhysicalPairedBranches_of_unitCyclePairedRepairs hrepairs

/--
[fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_unitCyclePairedRepairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMinimalCyclePhysicalRepair.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_unitCyclePairedRepairs_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale → Even scale → 12 * scale + 2 < 2 * (k + 3) → ∀ᶠ blocks in Filter.atTop, hardFloor ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hrepairs : SixVertexCanonicalPositiveEvenTraceUnitCyclePairedRepairs) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_unitCyclePairedRepairs hq hhard hcross hrepairs


-- created on 2026-10-23
