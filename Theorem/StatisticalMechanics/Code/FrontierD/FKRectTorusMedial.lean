/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusMedial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part3


namespace StatMech.FrontierD

@[simp] theorem fkRectConfigurationToMedialPairing_apply
    (R : FKRectTorus) (omega : R.Configuration)
    (v : R.medialTorus.Vertex) :
    fkRectConfigurationToMedialPairing R omega v =
      (omega (fkRectTorusMedialEdgeEquiv R v) ^^
        fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R v)) := rfl


end StatMech.FrontierD
