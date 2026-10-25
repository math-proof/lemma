/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part25


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_inputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    seed.selected (seed.inputState layer x) = seed.selected x := by
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.inputState
  split
  · exact seed.selected_branchSwap x
  · rfl


@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_outputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    seed.selected (seed.outputState layer x) = seed.selected x := by
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.outputState
  split
  · exact seed.selected_branchSwap x
  · rfl


@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_tauAdjusted
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (x : DoubledAlignedState omega eta) :
    seed.selected
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      seed.selected x := by
  let retie := orientedDartAlignedRetie homega heta hdegree x.1
  by_cases heq : retie.pairingP = retie.pairingQ
  · simp [sixVertexDegreeTwoTauAdjustedState, retie, heq]
  · simpa [sixVertexDegreeTwoTauAdjustedState, retie, heq] using
      seed.selected_branchSwap x


@[simp] theorem
    SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_sourceReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    seed.selected (seed.sourceReturnState layer x) =
      seed.selected (doubledAlignedFirstReturnPerm homega heta hdegree x) := by
  cases layer
  · rfl
  · exact seed.selected_tauAdjusted
      (doubledAlignedFirstReturnPerm homega heta hdegree x)


@[simp] theorem
    SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_activeReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    seed.selected (seed.activeReturnState layer x) =
      seed.selected (doubledAlignedFirstReturnPerm homega heta hdegree
        (seed.inputState layer x)) := by
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.activeReturnState
  rw [seed.selected_outputState, seed.selected_sourceReturnState]


theorem
    SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_activeReturnState_bne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta) :
    (seed.selected (seed.activeReturnState layer x) != seed.selected x) =
      seed.transitionBit
        (doubledAlignedFirstReturnPerm homega heta hdegree
          (seed.inputState layer x)) := by
  rw [seed.selected_activeReturnState]
  unfold SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionBit
  rw [Equiv.symm_apply_apply, seed.selected_inputState]


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.firstReturn_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart) :
    let mask := seed.retieMask layer
    let swapped := fkMedialBlackDartMaskSwap mask dart
    (finiteFirstReturn
        (fkMedialBlackBoundaryPerm (seed.targetPairing layer))
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨dart, hactive⟩).1 =
      (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree layer)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨swapped, (activeBlackDart_maskSwap_iff mask dart).mpr hactive⟩).1 := by
  classical
  let mask := seed.retieMask layer
  have hreturn := finiteFirstReturn_togglePairingMask_active
      (alignedRoutingLoopPairing homega heta hdegree layer) mask
      (fun d hd => by
        have hzero := (hdegree d.1.1).resolve_right hd
        have hnot : ¬ (sixVertexLocalDisagreementSides
            (sixVertexLocalIncomingPattern omega d.1.1)
            (sixVertexLocalIncomingPattern eta d.1.1)).card = 2 := by omega
        simp [mask, SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask,
          SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionVertex,
          SixVertexDegreeTwoSynchronizedHighChargeSeed.internalMismatchVertex,
          hnot]) dart hactive
  simpa [SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing, mask]
    using hreturn


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.firstReturn_slot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (x : DoubledAlignedState omega eta)
    (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
    (hslot : fkColoredBlackDartStrandSlotEquiv (seed.targetPairing layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) :
    fkColoredBlackDartStrandSlotEquiv (seed.targetPairing layer)
        ((finiteFirstReturn
          (fkMedialBlackBoundaryPerm (seed.targetPairing layer))
          (activeBlackDart (omega := omega) (eta := eta))
          ⟨dart, hactive⟩).1) =
      (doubledAlignedVertex (seed.activeReturnState layer x),
        doubledAlignedSlot homega heta hdegree layer
          (seed.activeReturnState layer x)) := by
  classical
  let sourcePairing := alignedRoutingLoopPairing homega heta hdegree layer
  let mask := seed.retieMask layer
  let targetPairing := seed.targetPairing layer
  let input := seed.inputState layer x
  let returned := seed.sourceReturnState layer input
  let swapped := fkMedialBlackDartMaskSwap mask dart
  have hpairing : targetPairing =
      fkMedialTogglePairingMask sourcePairing mask := rfl
  have hdart : dart =
      (fkColoredBlackDartStrandSlotEquiv targetPairing).symm
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x) := by
    apply (fkColoredBlackDartStrandSlotEquiv targetPairing).injective
    simpa [targetPairing] using hslot
  have hswapped : swapped =
      doubledAlignedBlackDart homega heta hdegree layer input := by
    dsimp only [swapped]
    rw [hdart, hpairing]
    exact fkMedialBlackDartMaskSwap_canonicalTargetState homega heta hdegree
      mask layer x
  have hswappedActive :
      activeBlackDart (omega := omega) (eta := eta) swapped :=
    (activeBlackDart_maskSwap_iff mask dart).mpr hactive
  have hstart :
      (⟨swapped, hswappedActive⟩ : {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d}) =
      doubledAlignedBlackDartEquiv homega heta hdegree layer input := by
    apply Subtype.ext
    exact hswapped
  have hsourceReturn :
      (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree layer)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨swapped, hswappedActive⟩).1 =
      doubledAlignedBlackDart homega heta hdegree layer returned := by
    rw [hstart]
    cases layer
    · exact congrArg Subtype.val
        (doubledAlignedFirstReturnPerm_false_arrival homega heta hdegree input).symm
    · exact congrArg Subtype.val
        (sixVertexDegreeTwoAlignedTrueFirstReturn_arrival homega heta hdegree
          input)
  have htargetReturn := seed.firstReturn_active layer dart hactive
  change (finiteFirstReturn
      (fkMedialBlackBoundaryPerm targetPairing)
      (activeBlackDart (omega := omega) (eta := eta))
      ⟨dart, hactive⟩).1 =
    (finiteFirstReturn
      (alignedBoundaryPerm homega heta hdegree layer)
      (activeBlackDart (omega := omega) (eta := eta))
      ⟨swapped, hswappedActive⟩).1 at htargetReturn
  change fkColoredBlackDartStrandSlotEquiv targetPairing
      ((finiteFirstReturn
        (fkMedialBlackBoundaryPerm targetPairing)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨dart, hactive⟩).1) = _
  rw [htargetReturn, hsourceReturn, hpairing,
    fkColoredBlackDartStrandSlotEquiv_togglePairingMask]
  simp only [Equiv.trans_apply]
  have hcoordinate :
      fkColoredBlackDartStrandSlotEquiv sourcePairing
          (doubledAlignedBlackDart homega heta hdegree layer returned) =
        (doubledAlignedVertex returned,
          doubledAlignedSlot homega heta hdegree layer returned) :=
    fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot _ _
  rw [hcoordinate,
    fkColoredParityMaskStrandSlotSwap_doubledAlignedState]
  rfl


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.targetBoundary
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) :
    fkColoredStrandSlotBoundaryPerm (seed.targetPairing layer) =
      (fkColoredParityMaskStrandSlotSwap (seed.retieMask layer) false).trans
        ((fkColoredStrandSlotBoundaryPerm
          (alignedRoutingLoopPairing homega heta hdegree layer)).trans
          (fkColoredParityMaskStrandSlotSwap
            (seed.retieMask layer) true)) := by
  exact fkColoredStrandSlotBoundaryPerm_togglePairingMask _ _


@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing_recover
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) :
    fkMedialTogglePairingMask (seed.targetPairing layer)
        (seed.retieMask layer) =
      alignedRoutingLoopPairing homega heta hdegree layer := by
  exact fkMedialTogglePairingMask_self _ _


@[simp] theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (v : T.Vertex)
    (hzero : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 0) :
    seed.retieMask layer v = false := by
  have hnot : ¬ (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 := by omega
  simp [SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask,
    SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionVertex,
    SixVertexDegreeTwoSynchronizedHighChargeSeed.internalMismatchVertex,
    hnot]


theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) (v : T.Vertex)
    (hzero : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 0) :
    seed.targetPairing layer v =
      alignedRoutingLoopPairing homega heta hdegree layer v := by
  simp [SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing,
    fkMedialTogglePairingMask, seed.retieMask_inactive layer v hzero]


end
end StatMech.FrontierD
