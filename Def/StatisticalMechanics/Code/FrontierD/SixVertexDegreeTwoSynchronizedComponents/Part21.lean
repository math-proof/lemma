/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part22


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.internalMismatchVertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (v : T.Vertex) : Bool :=
  if hv : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 then
    let d := orientedDisagreementDartAtActiveVertex homega heta v hv
    seed.selected (d, false) &&
      ((orientedDartAlignedRetie homega heta hdegree d).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree d).pairingQ)
  else false


end
end StatMech.FrontierD
