/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedActive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedInactive
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoAlignedActiveColor_false_branchSwap_bne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
        (doubledAlignedBranchSwap x)) =
      (sixVertexLocalIncomingPattern omega (doubledAlignedVertex x) 0 !=
        sixVertexLocalIncomingPattern omega (doubledAlignedVertex x) 1) := by
  rw [sixVertexDegreeTwoAlignedActiveColor,
    sixVertexDegreeTwoAlignedActiveColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor]
  rcases x with ⟨d, branch⟩
  simp only [doubledAlignedVertex, doubledAlignedBranchSwap,
    doubledAlignedSlot]
  cases branch <;>
    cases hp : fkMedialVertexParity d.1.1.1 <;>
    cases hs : orientedDartBoundaryAlignedSlot homega heta hdegree false d <;>
    simp [horizontalSlot, bne_comm]

theorem sixVertexDegreeTwoAlignedActiveColor_true_branchSwap_bne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true x !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
        (doubledAlignedBranchSwap x)) =
      (sixVertexLocalIncomingPattern eta (doubledAlignedVertex x) 0 !=
        sixVertexLocalIncomingPattern eta (doubledAlignedVertex x) 1) := by
  rw [sixVertexDegreeTwoAlignedActiveColor,
    sixVertexDegreeTwoAlignedActiveColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor]
  rcases x with ⟨d, branch⟩
  simp only [doubledAlignedVertex, doubledAlignedBranchSwap,
    doubledAlignedSlot]
  cases branch <;>
    cases hp : fkMedialVertexParity d.1.1.1 <;>
    cases hs : orientedDartBoundaryAlignedSlot homega heta hdegree true d <;>
    simp [horizontalSlot, bne_comm]

theorem sixVertexDegreeTwoCanonicalTransportedColor_rightHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let head := cut.cutRight.head hright
    let predecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
    sixVertexDegreeTwoCanonicalTransportedActiveColor homega heta hdegree
        middle homegaSector hetaSector hmiddle layer head =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer head ∧
    sixVertexDegreeTwoCanonicalTransportedActiveColor homega heta hdegree
        middle homegaSector hetaSector hmiddle layer predecessor =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree (!layer)
        predecessor := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let head := cut.cutRight.head hright
  let predecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
  have hselected := sixVertexDegreeTwoCanonicalSelected_rightHead homega heta
    hdegree middle homegaSector hetaSector hmiddle hleft hright
  change sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle head = false ∧
    sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle predecessor = true at hselected
  constructor
  · rw [sixVertexDegreeTwoCanonicalTransportedActiveColor,
      sixVertexDegreeTwoCanonicalTransportedColor_active, hselected.1]
    rfl
  · rw [sixVertexDegreeTwoCanonicalTransportedActiveColor,
      sixVertexDegreeTwoCanonicalTransportedColor_active, hselected.2]
    rfl

theorem sixVertexDegreeTwoCanonicalTransportedColor_leftHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let head := cut.cutLeft.head hleft
    let predecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
    sixVertexDegreeTwoCanonicalTransportedActiveColor homega heta hdegree
        middle homegaSector hetaSector hmiddle layer head =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree (!layer) head ∧
    sixVertexDegreeTwoCanonicalTransportedActiveColor homega heta hdegree
        middle homegaSector hetaSector hmiddle layer predecessor =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer
        predecessor := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let head := cut.cutLeft.head hleft
  let predecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
  have hselected := sixVertexDegreeTwoCanonicalSelected_leftHead homega heta
    hdegree middle homegaSector hetaSector hmiddle hleft hright
  change sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle head = true ∧
    sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle predecessor = false at hselected
  constructor
  · rw [sixVertexDegreeTwoCanonicalTransportedActiveColor,
      sixVertexDegreeTwoCanonicalTransportedColor_active, hselected.1]
    rfl
  · rw [sixVertexDegreeTwoCanonicalTransportedActiveColor,
      sixVertexDegreeTwoCanonicalTransportedColor_active, hselected.2]
    rfl

@[simp] theorem fkMedialBlackDartMaskSwap_vertex
    {T : EvenTorus} (mask : T.Vertex -> Bool) (dart : FKMedialBlackDart T) :
    (fkMedialBlackDartMaskSwap mask dart).1.1 = dart.1.1 := by
  by_cases hm : mask dart.1.1 <;>
    simp [fkMedialBlackDartMaskSwap, hm, fkMedialBlackDartSwap_self_vertex]

@[simp] theorem activeBlackDart_maskSwap_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (mask : T.Vertex -> Bool) (dart : FKMedialBlackDart T) :
    activeBlackDart (omega := omega) (eta := eta)
        (fkMedialBlackDartMaskSwap mask dart) ↔
      activeBlackDart (omega := omega) (eta := eta) dart := by
  unfold activeBlackDart
  rw [fkMedialBlackDartMaskSwap_vertex]


theorem finiteFirstReturn_togglePairingMask_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (pairing : FKMedialLoopPairing T) (mask : T.Vertex -> Bool)
    (hmask : forall (dart : FKMedialBlackDart T),
      Not (activeBlackDart (omega := omega) (eta := eta) dart) ->
        mask dart.1.1 = false)
    (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart) :
    let swapped := fkMedialBlackDartMaskSwap mask dart
    (finiteFirstReturn
        (fkMedialBlackBoundaryPerm (fkMedialTogglePairingMask pairing mask))
        (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1 =
      (finiteFirstReturn (fkMedialBlackBoundaryPerm pairing)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨swapped, (activeBlackDart_maskSwap_iff mask dart).mpr hactive⟩).1 := by
  let target := fkMedialBlackBoundaryPerm
    (fkMedialTogglePairingMask pairing mask)
  let source := fkMedialBlackBoundaryPerm pairing
  let swapped := fkMedialBlackDartMaskSwap mask dart
  have hswappedActive :
      activeBlackDart (omega := omega) (eta := eta) swapped := by
    exact (activeBlackDart_maskSwap_iff mask dart).mpr hactive
  let x : {d : FKMedialBlackDart T //
      activeBlackDart (omega := omega) (eta := eta) d} := ⟨dart, hactive⟩
  let y : {d : FKMedialBlackDart T //
      activeBlackDart (omega := omega) (eta := eta) d} :=
    ⟨swapped, hswappedActive⟩
  have htarget : target = source * fkMedialBlackDartMaskSwap mask := by
    exact fkMedialBlackBoundaryPerm_togglePairingMask pairing mask
  have hrelated := finiteFirstReturn_related_of_aligned_first target source
    (activeBlackDart (omega := omega) (eta := eta))
    (activeBlackDart (omega := omega) (eta := eta))
    (fun a b => a = b)
    (by intro a b hab; simpa [hab])
    (by
      intro a b hab ha hb
      subst b
      have hm : mask a.1.1 = false := hmask a ha
      rw [htarget]
      simp [Equiv.Perm.mul_apply, fkMedialBlackDartMaskSwap, hm])
    x y
    (by
      rw [htarget]
      simp [x, y, swapped, Equiv.Perm.mul_apply])
  exact hrelated

theorem sixVertexDegreeTwoCanonicalExpanded_firstReturn_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart) :
    let mask := sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
    let swapped := fkMedialBlackDartMaskSwap mask dart
    (finiteFirstReturn
        (fkMedialBlackBoundaryPerm
          (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
            middle homegaSector hetaSector hmiddle layer))
        (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1 =
      (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree layer)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨swapped, (activeBlackDart_maskSwap_iff mask dart).mpr hactive⟩).1 := by
  let mask := sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
    middle homegaSector hetaSector hmiddle layer
  rw [sixVertexDegreeTwoCanonicalExpandedTargetPairing_eq_toggleMask]
  exact finiteFirstReturn_togglePairingMask_active
    (alignedRoutingLoopPairing homega heta hdegree layer) mask
    (fun d hd => sixVertexDegreeTwoCanonicalExpandedRetieMask_inactive homega
      heta hdegree middle homegaSector hetaSector hmiddle layer d hd)
    dart hactive


theorem fkMedialBlackDartMaskSwap_targetSlot
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (mask : T.Vertex -> Bool) (slot : T.Vertex × Bool) :
    fkColoredBlackDartStrandSlotEquiv pairing
        (fkMedialBlackDartMaskSwap mask
          ((fkColoredBlackDartStrandSlotEquiv
            (fkMedialTogglePairingMask pairing mask)).symm slot)) =
      fkColoredParityMaskStrandSlotSwap mask false slot := by
  let source := fkColoredBlackDartStrandSlotEquiv pairing
  let target := fkColoredBlackDartStrandSlotEquiv
    (fkMedialTogglePairingMask pairing mask)
  let blackSwap := fkColoredParityMaskStrandSlotSwap mask true
  let whiteSwap := fkColoredParityMaskStrandSlotSwap mask false
  let dart := target.symm slot
  have htarget := fkColoredBlackDartStrandSlotEquiv_togglePairingMask
    pairing mask
  have hdart : blackSwap (source dart) = slot := by
    change (source.trans blackSwap) dart = slot
    rw [← htarget]
    exact target.apply_symm_apply slot
  rw [fkColoredBlackDartStrandSlotEquiv_blackDartMaskSwap]
  change whiteSwap (blackSwap (source dart)) = whiteSwap slot
  rw [hdart]

theorem fkMedialBlackDartMaskSwap_canonicalTargetState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (mask : T.Vertex -> Bool) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    fkMedialBlackDartMaskSwap mask
        ((fkColoredBlackDartStrandSlotEquiv
          (fkMedialTogglePairingMask
            (alignedRoutingLoopPairing homega heta hdegree layer) mask)).symm
          (doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x)) =
      doubledAlignedBlackDart homega heta hdegree layer
        (if mask (doubledAlignedVertex x) &&
            (fkMedialVertexParity (doubledAlignedVertex x) == false) then
          doubledAlignedBranchSwap x else x) := by
  apply (fkColoredBlackDartStrandSlotEquiv
    (alignedRoutingLoopPairing homega heta hdegree layer)).injective
  rw [fkMedialBlackDartMaskSwap_targetSlot]
  simp only [doubledAlignedBlackDart,
    fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot]
  by_cases hm : mask (doubledAlignedVertex x) <;>
    cases hp : fkMedialVertexParity (doubledAlignedVertex x)
  · simpa [fkColoredParityMaskStrandSlotSwap, hm, hp] using
      fkColoredVertexStrandSlotSwap_doubledAlignedSlot
        homega heta hdegree layer x
  · simp [fkColoredParityMaskStrandSlotSwap, hm, hp]
  · simp [fkColoredParityMaskStrandSlotSwap, hm, hp]
  · simp [fkColoredParityMaskStrandSlotSwap, hm, hp]

theorem fkColoredParityMaskStrandSlotSwap_doubledAlignedState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (mask : T.Vertex -> Bool) (parity layer : Bool)
    (x : DoubledAlignedState omega eta) :
    fkColoredParityMaskStrandSlotSwap mask parity
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x) =
      (doubledAlignedVertex
          (if mask (doubledAlignedVertex x) &&
              (fkMedialVertexParity (doubledAlignedVertex x) == parity) then
            doubledAlignedBranchSwap x else x),
        doubledAlignedSlot homega heta hdegree layer
          (if mask (doubledAlignedVertex x) &&
              (fkMedialVertexParity (doubledAlignedVertex x) == parity) then
            doubledAlignedBranchSwap x else x)) := by
  by_cases hm : mask (doubledAlignedVertex x) <;>
    cases hp : fkMedialVertexParity (doubledAlignedVertex x) <;>
    cases parity
  all_goals simp [fkColoredParityMaskStrandSlotSwap, hm, hp]
  all_goals first
    | exact fkColoredVertexStrandSlotSwap_doubledAlignedSlot
        homega heta hdegree layer x
    | rfl

end
end StatMech.FrontierD
