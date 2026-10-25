/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part22


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    seed.retieMask layer (doubledAlignedVertex x) =
      ((seed.transitionBit (x.1, false) || seed.transitionBit (x.1, true)) ||
        (seed.selected x &&
          ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
            (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ))) := by
  rw [SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask,
    seed.transitionVertex_active x, seed.internalMismatchVertex_active x]


theorem
    SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_eq_true_of_transition
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta)
    (htransition : seed.transitionBit x = true) :
    seed.retieMask layer (doubledAlignedVertex x) = true := by
  rw [seed.retieMask_active layer x]
  rcases x with ⟨dart, branch⟩
  cases branch
  · simp [htransition]
  · simp [htransition]


theorem
    SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_eq_true_of_internal
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta)
    (hselected : seed.selected x = true)
    (hpairing :
      ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) = true) :
    seed.retieMask layer (doubledAlignedVertex x) = true := by
  rw [seed.retieMask_active layer x, hselected, hpairing]
  simp


end
end StatMech.FrontierD
