/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part5


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoSynchronizedComponentPhysicalInputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    DoubledAlignedState omega eta :=
  if sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta
      hdegree component layer (doubledAlignedVertex x) &&
      (fkMedialVertexParity (doubledAlignedVertex x) == false) then
    doubledAlignedBranchSwap x else x


noncomputable def sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (_component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    DoubledAlignedState omega eta :=
  if layer then
    sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree x
  else doubledAlignedFirstReturnPerm homega heta hdegree x


end
end StatMech.FrontierD
