/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part6


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoSynchronizedComponentPhysicalOutputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    DoubledAlignedState omega eta :=
  if sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta
      hdegree component layer (doubledAlignedVertex x) &&
      (fkMedialVertexParity (doubledAlignedVertex x) == true) then
    doubledAlignedBranchSwap x else x


noncomputable def sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    DoubledAlignedState omega eta :=
  sixVertexDegreeTwoSynchronizedComponentPhysicalOutputState homega heta hdegree
    component layer
    (sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState homega
      heta hdegree component layer
      (sixVertexDegreeTwoSynchronizedComponentPhysicalInputState homega heta
        hdegree component layer x))

end
end StatMech.FrontierD
