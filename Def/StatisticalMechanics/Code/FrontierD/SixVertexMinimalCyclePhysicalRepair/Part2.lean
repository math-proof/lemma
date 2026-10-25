/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMinimalCyclePhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisjointCapPhysicalRepair.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMinimalCyclePhysicalRepair


namespace StatMech.FrontierD

noncomputable section

def SixVertexDisjointCapUnitRepair.toUnitCycleRepair
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexDisjointCapUnitRepair omega eta loopGrade) :
    SixVertexTwoLayerUnitCycleRepair omega eta loopGrade where
  first := repair.first.cycle
  second := repair.second.cycle
  first_follows := repair.first.cycle_follows
  second_follows := repair.second.cycle_follows
  tail_disjoint := repair.cycle_tail_disjoint
  first_seam_flow := repair.first_seam_flow
  second_seam_flow := repair.second_seam_flow
  fine := repair.fine
  loopGrade_eq := repair.loopGrade_eq

end
end StatMech.FrontierD
