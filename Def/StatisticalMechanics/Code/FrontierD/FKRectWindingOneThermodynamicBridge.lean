/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingOneResidualLower
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorThermodynamicBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectUnitLeftBarrier.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceChainWindingUpper.Part2
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def fkRectCriticalWindingOneMass (R : FKRectTorus) (q : Real) : Real :=
  fkRectCriticalEventMass R q
    {omega | fkRectUnorientedVerticalWindingNumber R omega = 1}


end
end StatMech.FrontierD
