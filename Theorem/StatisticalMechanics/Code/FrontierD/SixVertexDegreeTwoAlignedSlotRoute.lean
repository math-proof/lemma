/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part7
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotRoute


namespace StatMech.FrontierD

noncomputable section

theorem fkColoredSideSlot_eq_strandSlotOfBlackDart
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (dart : FKMedialBlackDart T) :
    fkColoredSideSlot (pairing dart.1.1) dart.1.2 =
      strandSlotOfBlackDart pairing dart := by
  rcases dart with ⟨⟨v, side⟩, hdart⟩
  cases side <;> cases hp : pairing v <;>
    cases hv : fkMedialVertexParity v <;>
    simp [fkColoredSideSlot, strandSlotOfBlackDart,
      fkMedialBlackSideIndex, fkMedialCheckerColor,
      fkMedialSideVertical, hp, hv] at hdart ⊢

@[simp] theorem strandSlotOfBlackDart_blackDartOfStrandSlot
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (slot : T.Vertex × Bool) :
    strandSlotOfBlackDart pairing
        (blackDartOfStrandSlot pairing slot) = slot.2 := by
  let factor := fkMedialVertexParity slot.1 && !pairing slot.1
  have hfixed := congrArg Prod.snd
    ((fkMedialBlackDartEquivVertexBool T).apply_symm_apply
      (slot.1, blackSideIndexOfStrandSlot
        (fkMedialVertexParity slot.1) (pairing slot.1) slot.2))
  change fkMedialBlackSideIndex
      (blackDartOfStrandSlot pairing slot).1.2 =
    blackSideIndexOfStrandSlot
      (fkMedialVertexParity slot.1) (pairing slot.1) slot.2 at hfixed
  unfold strandSlotOfBlackDart
  rw [blackDartOfStrandSlot_vertex, hfixed]
  cases hp : pairing slot.1 <;>
    cases hv : fkMedialVertexParity slot.1 <;>
    cases hs : slot.2 <;>
    simp [blackSideIndexOfStrandSlot]

@[simp] theorem fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (slot : T.Vertex × Bool) :
    fkColoredBlackDartStrandSlotEquiv pairing
        (blackDartOfStrandSlot pairing slot) = slot := by
  apply Prod.ext
  · exact blackDartOfStrandSlot_vertex pairing slot
  · rw [fkColoredBlackDartStrandSlotEquiv_apply]
    change fkColoredSideSlot
        (pairing (blackDartOfStrandSlot pairing slot).1.1)
        (blackDartOfStrandSlot pairing slot).1.2 = slot.2
    rw [fkColoredSideSlot_eq_strandSlotOfBlackDart,
      strandSlotOfBlackDart_blackDartOfStrandSlot]

@[simp] theorem fkColoredVertexStrandSlotSwap_doubledAlignedSlot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    fkColoredVertexStrandSlotSwap (doubledAlignedVertex x)
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x) =
      (doubledAlignedVertex (doubledAlignedBranchSwap x),
        doubledAlignedSlot homega heta hdegree layer
          (doubledAlignedBranchSwap x)) := by
  rw [doubledAlignedVertex_branchSwap,
    doubledAlignedSlot_branchSwap]
  rcases doubledAlignedVertex x with ⟨i, j⟩
  cases hs : doubledAlignedSlot homega heta hdegree layer x <;>
    simp [fkColoredVertexStrandSlotSwap]


theorem fkMedialBlackDartSwap_doubledAlignedBlackDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    fkMedialBlackDartSwap (doubledAlignedVertex x)
        (doubledAlignedBlackDart homega heta hdegree layer x) =
      doubledAlignedBlackDart homega heta hdegree layer
        (doubledAlignedBranchSwap x) := by
  apply (fkColoredBlackDartStrandSlotEquiv
    (alignedRoutingLoopPairing homega heta hdegree layer)).injective
  rw [fkColoredBlackDartStrandSlot_blackSwap]
  simp only [doubledAlignedBlackDart,
    fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot]
  exact fkColoredVertexStrandSlotSwap_doubledAlignedSlot
    homega heta hdegree layer x

theorem blackSideIndex_boundaryAlignedSlotQRaw
    (pairingP pairingQ vertexParity branch : Bool) (d : Fin 4) :
    blackSideIndexOfStrandSlot vertexParity pairingQ
        (if branch then
          !boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d
        else boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) =
      if pairingP = pairingQ then
        blackSideIndexOfStrandSlot vertexParity pairingP
          (if branch then !strandSlot pairingP d else strandSlot pairingP d)
      else
        blackSideIndexOfStrandSlot vertexParity pairingP
          (if !branch then !strandSlot pairingP d else strandSlot pairingP d) := by
  cases pairingP <;> cases pairingQ <;> cases vertexParity <;>
    cases branch <;> fin_cases d <;>
      decide


theorem doubledAlignedBlackDart_true_eq_false_or_branchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    let retie := orientedDartAlignedRetie homega heta hdegree x.1
    doubledAlignedBlackDart homega heta hdegree true x =
      if retie.pairingP = retie.pairingQ then
        doubledAlignedBlackDart homega heta hdegree false x
      else
        doubledAlignedBlackDart homega heta hdegree false
          (doubledAlignedBranchSwap x) := by
  rcases x with ⟨d, branch⟩
  let retie := orientedDartAlignedRetie homega heta hdegree d
  let v := d.1.1.1
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree d.1
  let d0 := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd0 : d0 = d := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d0 d rfl
  have hP := alignedRoutingPairing_eq_at_active
    homega heta hdegree false v hactive
  have hQ := alignedRoutingPairing_eq_at_active
    homega heta hdegree true v hactive
  change alignedRoutingLoopPairing homega heta hdegree false v =
      (orientedDartAlignedRetie homega heta hdegree d0).pairingP at hP
  change alignedRoutingLoopPairing homega heta hdegree true v =
      (orientedDartAlignedRetie homega heta hdegree d0).pairingQ at hQ
  rw [hd0] at hP hQ
  change doubledAlignedBlackDart homega heta hdegree true (d, branch) =
    if retie.pairingP = retie.pairingQ then
      doubledAlignedBlackDart homega heta hdegree false (d, branch)
    else doubledAlignedBlackDart homega heta hdegree false
      (doubledAlignedBranchSwap (d, branch))
  by_cases heq : retie.pairingP = retie.pairingQ
  · rw [if_pos heq]
    apply (fkMedialBlackDartEquivVertexBool T).injective
    simp only [doubledAlignedBlackDart, blackDartOfStrandSlot,
      Equiv.apply_symm_apply, doubledAlignedVertex, doubledAlignedSlot]
    rw [hP, hQ]
    apply Prod.ext
    · rfl
    · have h := blackSideIndex_boundaryAlignedSlotQRaw retie.pairingP
        retie.pairingQ (fkMedialVertexParity v) branch d.1.1.2
      rwa [if_pos heq] at h
  · rw [if_neg heq]
    apply (fkMedialBlackDartEquivVertexBool T).injective
    simp only [doubledAlignedBlackDart, blackDartOfStrandSlot,
      Equiv.apply_symm_apply, doubledAlignedVertex,
      doubledAlignedBranchSwap, doubledAlignedSlot]
    rw [hP, hQ]
    apply Prod.ext
    · rfl
    · have h := blackSideIndex_boundaryAlignedSlotQRaw retie.pairingP
        retie.pairingQ (fkMedialVertexParity v) branch d.1.1.2
      rwa [if_neg heq] at h


end
end StatMech.FrontierD
