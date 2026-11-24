module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisjointCapPhysicalRepair.Part3
public import Structure.StatisticalMechanics.Code.FrontierD.SixVertexMinimalCyclePhysicalRepair


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMinimalCyclePhysicalRepair.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def SixVertexTwoLayerUnitCycleRepair.target
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {loopGrade : (SixVertexArrows T × SixVertexArrows T) → Nat × Nat}
    (repair : SixVertexTwoLayerUnitCycleRepair omega eta loopGrade) :
    SixVertexArrows T × SixVertexArrows T :=
  (sixVertexTorusFlip repair.first.mask omega,
    sixVertexTorusFlip repair.second.mask eta)

end
end StatMech.FrontierD
