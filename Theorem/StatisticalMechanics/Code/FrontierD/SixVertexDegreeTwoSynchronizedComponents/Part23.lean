/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part21


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.internalMismatchVertex_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) :
    seed.internalMismatchVertex (doubledAlignedVertex x) =
      (seed.selected x &&
        ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
          (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ)) := by
  let v := doubledAlignedVertex x
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd : d = x.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d x.1 rfl
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.internalMismatchVertex
  rw [dif_pos hactive]
  change orientedDisagreementDartAtActiveVertex homega heta v hactive = x.1 at hd
  rw [hd]
  rcases x with ⟨dart, branch⟩
  cases branch
  · rfl
  · have hs : seed.selected (dart, false) = seed.selected (dart, true) := by
      simpa [doubledAlignedBranchSwap] using
        (seed.selected_branchSwap (dart, false)).symm
    dsimp only
    rw [hs]


end
end StatMech.FrontierD
