/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisjointCapPhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAgreementCapEndpoint.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDisjointCapPhysicalRepair


namespace StatMech.FrontierD

noncomputable section

structure SixVertexFollowedAgreementCapCertificate
    {T : EvenTorus} (omega eta : SixVertexArrows T) where
  arc : SixVertexDirectedSimpleArc T
  cap : SixVertexDirectedSimpleArc T
  cycle : SixVertexDirectedSimpleCycle T
  arc_follows : arc.Follows omega
  arc_disagrees : forall i, Not ((arc.edge i).IsAgreement omega eta)
  cap_follows : cap.Follows omega
  cap_agrees : cap.IsAgreement omega eta
  cap_start : cap.start = arc.finish
  cap_finish : cap.finish = arc.start
  tail_disjoint : forall i j, (arc.edge i).tail != (cap.edge j).tail
  physical_disjoint : forall i j,
    (arc.edge i).physical != (cap.edge j).physical
  cycle_mask : cycle.mask = sixVertexTorusMaskXor arc.mask cap.mask
  cycle_follows : cycle.Follows omega


structure SixVertexDisjointCapUnitRepair
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat) where
  first : SixVertexFollowedAgreementCapCertificate omega eta
  second : SixVertexFollowedAgreementCapCertificate eta omega
  cycle_tail_disjoint : forall i j,
    (first.cycle.edge i).tail != (second.cycle.edge j).tail
  first_seam_flow :
    (∑ column : Fin T.width,
      first.cycle.verticalFlow (column, svFinLast T.height_pos)) = -1
  second_seam_flow :
    (∑ column : Fin T.width,
      second.cycle.verticalFlow (column, svFinLast T.height_pos)) = 1
  fine : sixVertexHorizontalPairBoundedFineRowProfile
      (omega.horizontal, eta.horizontal) =
    sixVertexHorizontalPairBoundedFineRowProfile
      ((sixVertexTorusFlip first.cycle.mask omega).horizontal,
        (sixVertexTorusFlip second.cycle.mask eta).horizontal)
  loopGrade_eq : loopGrade
      (sixVertexTorusFlip first.cycle.mask omega,
        sixVertexTorusFlip second.cycle.mask eta) = loopGrade (omega, eta)


end
end StatMech.FrontierD
