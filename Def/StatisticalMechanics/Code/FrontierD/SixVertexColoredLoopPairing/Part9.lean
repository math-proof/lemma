/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part11


namespace StatMech.FrontierD

noncomputable section

def fkColoredLocalPairCrossIf
    (cross : Bool)
    (pair : FKColoredLocalPairing × FKColoredLocalPairing) :
    FKColoredLocalPairing × FKColoredLocalPairing :=
  if cross then fkColoredLocalPairReconnection pair else pair

end
end StatMech.FrontierD
