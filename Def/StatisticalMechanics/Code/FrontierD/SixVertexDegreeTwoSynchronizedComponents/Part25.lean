/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part26


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.outputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    DoubledAlignedState omega eta :=
  if seed.retieMask layer (doubledAlignedVertex x) &&
      (fkMedialVertexParity (doubledAlignedVertex x) == true) then
    doubledAlignedBranchSwap x else x


noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.activeReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    DoubledAlignedState omega eta :=
  seed.outputState layer
    (seed.sourceReturnState layer (seed.inputState layer x))


end
end StatMech.FrontierD
