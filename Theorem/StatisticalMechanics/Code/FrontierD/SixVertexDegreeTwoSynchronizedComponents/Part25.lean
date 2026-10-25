/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part23


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (v : T.Vertex)
    (hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2) :
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let transition := seed.transitionVertex v
    let internal := seed.internalMismatchVertex v
    seed.targetPairing layer v =
      if transition || internal then
        !(if layer then
          (orientedDartAlignedRetie homega heta hdegree d).pairingQ
        else (orientedDartAlignedRetie homega heta hdegree d).pairingP)
      else if layer then
        (orientedDartAlignedRetie homega heta hdegree d).pairingQ
      else (orientedDartAlignedRetie homega heta hdegree d).pairingP := by
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hsource := alignedRoutingPairing_eq_at_active
    homega heta hdegree layer v hactive
  change alignedRoutingLoopPairing homega heta hdegree layer v =
    (if layer then (orientedDartAlignedRetie homega heta hdegree d).pairingQ
      else (orientedDartAlignedRetie homega heta hdegree d).pairingP) at hsource
  rw [SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing,
    fkMedialTogglePairingMask, hsource]
  rfl


end
end StatMech.FrontierD
