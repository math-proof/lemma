/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisjointCapPhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAgreementCapEndpoint.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch.Part7
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDisjointCapPhysicalRepair


namespace StatMech.FrontierD

noncomputable section

def SixVertexDisjointCapUnitRepair.target
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexDisjointCapUnitRepair omega eta loopGrade) :
    SixVertexArrows T × SixVertexArrows T :=
  (sixVertexTorusFlip repair.first.cycle.mask omega,
    sixVertexTorusFlip repair.second.cycle.mask eta)

end
end StatMech.FrontierD
