/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTransitionRetieExact.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySlotColorInvariant.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalUnitRoute.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part9


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoAlignedFalseDartOfSlot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (slot : T.Vertex × Bool) : FKMedialBlackDart T :=
  if layer then
    (alignedBlackDartLayerSwap homega heta hdegree).symm
      ((fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree true)).symm slot)
  else
    (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree false)).symm slot

end
end StatMech.FrontierD
