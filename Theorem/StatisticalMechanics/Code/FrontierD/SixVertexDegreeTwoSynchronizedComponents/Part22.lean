/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part20


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionVertex_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) :
    seed.transitionVertex (doubledAlignedVertex x) =
      (seed.transitionBit (x.1, false) ||
        seed.transitionBit (x.1, true)) := by
  let v := doubledAlignedVertex x
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd : d = x.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d x.1 rfl
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionVertex
  rw [dif_pos hactive]
  change orientedDisagreementDartAtActiveVertex homega heta v hactive = x.1 at hd
  rw [hd]
  rfl


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionVertex_eq_bit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (d : SixVertexOrientedDisagreementDart omega eta)
    (hsync : seed.synchronizedAt d) :
    seed.transitionVertex d.1.1.1 = seed.transitionBit (d, false) := by
  have h := seed.transitionVertex_active (d, false)
  change seed.transitionVertex d.1.1.1 = _ at h
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.synchronizedAt at hsync
  rw [h, hsync, Bool.or_self]


end
end StatMech.FrontierD
