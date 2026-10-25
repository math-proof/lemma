/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part10


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) : Bool :=
  fkColoredLayeredSlotColor
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
    (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree
      component
      (layer, doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x))


end
end StatMech.FrontierD
