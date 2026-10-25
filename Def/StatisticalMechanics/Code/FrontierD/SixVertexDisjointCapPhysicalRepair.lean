/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisjointCapPhysicalRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAgreementCapEndpoint.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenPhysicalPairedBranch.Part7
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDisjointCapPhysicalRepair


namespace StatMech.FrontierD

noncomputable section

def SixVertexDirectedSimpleArc.mask
    {T : EvenTorus} (arc : SixVertexDirectedSimpleArc T) :
    SixVertexArrows T where
  horizontal base := decide
    (exists i, (arc.edge i).physical = (false, base))
  vertical base := decide
    (exists i, (arc.edge i).physical = (true, base))


end
end StatMech.FrontierD
