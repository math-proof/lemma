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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part7


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoAlignedFalseDartSlotSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (mask : T.Vertex -> Bool) (parity layer : Bool)
    (dart : FKMedialBlackDart T) : FKMedialBlackDart T :=
  if mask dart.1.1 && (fkMedialVertexParity dart.1.1 == parity) then
    if layer then
      (alignedBlackDartLayerSwap homega heta hdegree).symm
        (fkMedialBlackDartSwap dart.1.1
          (alignedBlackDartLayerSwap homega heta hdegree dart))
    else fkMedialBlackDartSwap dart.1.1 dart
  else dart

end
end StatMech.FrontierD
