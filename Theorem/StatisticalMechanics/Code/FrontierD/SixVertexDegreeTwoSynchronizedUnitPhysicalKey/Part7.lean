/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part6


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector_inputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component
        (sixVertexDegreeTwoSynchronizedComponentPhysicalInputState homega heta
          hdegree component layer x) =
      sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component x := by
  unfold sixVertexDegreeTwoSynchronizedComponentPhysicalInputState
  split
  · exact sixVertexDegreeTwoSynchronizedComponentDoubledSelector_branchSwap
      homega heta hdegree component x
  · rfl

@[simp] theorem
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector_outputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component
        (sixVertexDegreeTwoSynchronizedComponentPhysicalOutputState homega heta
          hdegree component layer x) =
      sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component x := by
  unfold sixVertexDegreeTwoSynchronizedComponentPhysicalOutputState
  split
  · exact sixVertexDegreeTwoSynchronizedComponentDoubledSelector_branchSwap
      homega heta hdegree component x
  · rfl

@[simp] theorem
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector_tauAdjusted
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component x := by
  let retie := orientedDartAlignedRetie homega heta hdegree x.1
  by_cases heq : retie.pairingP = retie.pairingQ
  · simp [sixVertexDegreeTwoTauAdjustedState, retie, heq]
  · simpa [sixVertexDegreeTwoTauAdjustedState, retie, heq] using
      (sixVertexDegreeTwoSynchronizedComponentDoubledSelector_branchSwap
        homega heta hdegree component x)

@[simp] theorem
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector_sourceReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component
        (sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState
          homega heta hdegree component layer x) =
      sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component (doubledAlignedFirstReturnPerm homega heta hdegree x) := by
  cases layer
  · rfl
  · exact sixVertexDegreeTwoSynchronizedComponentDoubledSelector_tauAdjusted
      homega heta hdegree component
      (doubledAlignedFirstReturnPerm homega heta hdegree x)

@[simp] theorem
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector_returnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component
        (sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState homega heta
          hdegree component layer x) =
      sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component (doubledAlignedFirstReturnPerm homega heta hdegree
          (sixVertexDegreeTwoSynchronizedComponentPhysicalInputState homega heta
            hdegree component layer x)) := by
  unfold sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState
  rw [sixVertexDegreeTwoSynchronizedComponentDoubledSelector_outputState,
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector_sourceReturnState]


theorem sixVertexDegreeTwoSynchronizedComponentDoubledSelector_returnState_bne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    (sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component
        (sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState homega heta
          hdegree component layer x) !=
      sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree
        component x) =
      sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree
        component (doubledAlignedFirstReturnPerm homega heta hdegree
          (sixVertexDegreeTwoSynchronizedComponentPhysicalInputState homega heta
            hdegree component layer x)) := by
  rw [sixVertexDegreeTwoSynchronizedComponentDoubledSelector_returnState]
  unfold sixVertexDegreeTwoSynchronizedComponentTransitionBit
  rw [Equiv.symm_apply_apply,
    sixVertexDegreeTwoSynchronizedComponentDoubledSelector_inputState]


theorem sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_slot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool) (x : DoubledAlignedState omega eta)
    (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
    (hslot : fkColoredBlackDartStrandSlotEquiv
      (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
        hdegree component layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) :
    fkColoredBlackDartStrandSlotEquiv
        (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega
          heta hdegree component layer)
        ((finiteFirstReturn
          (fkMedialBlackBoundaryPerm
            (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing
              homega heta hdegree component layer))
          (activeBlackDart (omega := omega) (eta := eta))
          ⟨dart, hactive⟩).1) =
      (doubledAlignedVertex
          (sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState homega
            heta hdegree component layer x),
        doubledAlignedSlot homega heta hdegree layer
          (sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState homega
            heta hdegree component layer x)) := by
  classical
  let sourcePairing := alignedRoutingLoopPairing homega heta hdegree layer
  let mask := sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega
    heta hdegree component layer
  let targetPairing :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
      hdegree component layer
  let input := sixVertexDegreeTwoSynchronizedComponentPhysicalInputState homega
    heta hdegree component layer x
  let returned :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState homega
      heta hdegree component layer input
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
        (doubledAlignedFirstReturnPerm_false_arrival homega heta hdegree
          input).symm
    · exact congrArg Subtype.val
        (sixVertexDegreeTwoAlignedTrueFirstReturn_arrival homega heta hdegree
          input)
  have htargetReturn :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_active homega
      heta hdegree component layer dart hactive
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


end
end StatMech.FrontierD
