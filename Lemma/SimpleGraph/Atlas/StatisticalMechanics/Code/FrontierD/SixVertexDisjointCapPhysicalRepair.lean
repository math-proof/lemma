import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexDisjointCapPhysicalRepair
open StatMech StatMech.FrontierD StatMech.FrontierD.SixVertexDisjointCapUnitRepair


/--
[target_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisjointCapPhysicalRepair.lean)
-/
@[path]
private lemma target_ice_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
  {repair : SixVertexDisjointCapUnitRepair omega eta loopGrade}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule) :
-- imply
  repair.target.1.IceRule ∧ repair.target.2.IceRule := by
-- proof
  apply StatMech.FrontierD.SixVertexDisjointCapUnitRepair.target_ice repair homega heta

/--
[first_upCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisjointCapPhysicalRepair.lean)
-/
@[path]
private lemma first_upCount_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
  {repair : SixVertexDisjointCapUnitRepair omega eta loopGrade} :
-- imply
  (sixVertexUpCount (svTorusVerticalRows T repair.target.1 (svFinLast T.height_pos)) : Int) = (sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) : Int) + 1 := by
-- proof
  apply StatMech.FrontierD.SixVertexDisjointCapUnitRepair.first_upCount repair

/--
[second_upCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisjointCapPhysicalRepair.lean)
-/
@[path]
private lemma second_upCount_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
  {repair : SixVertexDisjointCapUnitRepair omega eta loopGrade} :
-- imply
  (sixVertexUpCount (svTorusVerticalRows T repair.target.2 (svFinLast T.height_pos)) : Int) = (sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) : Int) - 1 := by
-- proof
  apply StatMech.FrontierD.SixVertexDisjointCapUnitRepair.second_upCount repair

/--
[target_twoCycleFine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisjointCapPhysicalRepair.lean)
-/
@[path]
private lemma target_twoCycleFine_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
  {repair : SixVertexDisjointCapUnitRepair omega eta loopGrade} :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated (omega, eta) repair.target := by
-- proof
  apply StatMech.FrontierD.SixVertexDisjointCapUnitRepair.target_twoCycleFine repair

/--
[sixVertexDisjointCapPhysicalTarget_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisjointCapPhysicalRepair.lean)
-/
@[path]
private lemma sixVertexDisjointCapPhysicalTarget_arrows_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {source : SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt}
  {repair : SixVertexDisjointCapUnitRepair source.1.1 source.2.1 sixVertexPhysicalArrowPairGrade} :
-- imply
  ((sixVertexDisjointCapPhysicalTarget source repair).1.1, (sixVertexDisjointCapPhysicalTarget source repair).2.1) = repair.target := by
-- proof
  apply StatMech.FrontierD.sixVertexDisjointCapPhysicalTarget_arrows source repair

/--
[canonicalPhysicalPairedBranches_of_disjointCapPairedRepairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisjointCapPhysicalRepair.lean)
-/
@[path]
private lemma canonicalPhysicalPairedBranches_of_disjointCapPairedRepairs_eq
-- given
  (hrepairs : SixVertexCanonicalPositiveEvenTraceDisjointCapPairedRepairs) :
-- imply
  SixVertexCanonicalPositiveEvenTracePhysicalPairedBranches := by
-- proof
  apply StatMech.FrontierD.canonicalPhysicalPairedBranches_of_disjointCapPairedRepairs hrepairs

/--
[fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_disjointCapPairedRepairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisjointCapPhysicalRepair.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_disjointCapPairedRepairs_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale → Even scale → 12 * scale + 2 < 2 * (k + 3) → ∀ᶠ blocks in Filter.atTop, hardFloor ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hrepairs : SixVertexCanonicalPositiveEvenTraceDisjointCapPairedRepairs) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_disjointCapPairedRepairs hq hhard hcross hrepairs


-- created on 2026-10-23
