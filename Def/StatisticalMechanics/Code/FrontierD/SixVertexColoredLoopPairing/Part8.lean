/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part10


namespace StatMech.FrontierD

noncomputable section

def fkColoredLocalPairCTypeCount
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) : Nat :=
  (if pair.1.west = pair.1.east then 1 else 0) +
    (if pair.2.west = pair.2.east then 1 else 0)

end
end StatMech.FrontierD
