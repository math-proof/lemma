/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part24


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.sourceReturnState_color
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer
        (seed.sourceReturnState layer x) =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer x := by
  cases layer
  · simpa [SixVertexDegreeTwoSynchronizedHighChargeSeed.sourceReturnState,
      sixVertexDegreeTwoAlignedActiveColor] using
      (sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_false
        homega heta hdegree x).symm
  · let y := doubledAlignedFirstReturnPerm homega heta hdegree x
    let retie := orientedDartAlignedRetie homega heta hdegree y.1
    have h := sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_true
      homega heta hdegree x
    change sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true x =
      if retie.pairingP = retie.pairingQ then
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true y
      else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
        (doubledAlignedBranchSwap y) at h
    rw [SixVertexDegreeTwoSynchronizedHighChargeSeed.sourceReturnState,
      if_pos rfl, sixVertexDegreeTwoAlignedTrueFirstReturnState]
    change sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
      (if retie.pairingP = retie.pairingQ then y
        else doubledAlignedBranchSwap y) = _
    by_cases heq : retie.pairingP = retie.pairingQ
    · rw [if_pos heq] at h ⊢
      exact h.symm
    · rw [if_neg heq] at h ⊢
      exact h.symm


end
end StatMech.FrontierD
