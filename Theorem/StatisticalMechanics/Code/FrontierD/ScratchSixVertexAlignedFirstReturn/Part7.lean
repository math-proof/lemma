/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Def.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part8
open StatMech.FrontierD


namespace ScratchLocalRetieC

theorem blackDartOfStrandSlot_injective
    {T : EvenTorus} (pairing : FKMedialLoopPairing T) :
    Function.Injective (blackDartOfStrandSlot pairing) := by
  rintro ⟨v, side⟩ ⟨w, side'⟩ h
  have hfixed := congrArg (fkMedialBlackDartEquivVertexBool T) h
  simp only [blackDartOfStrandSlot, Equiv.apply_symm_apply] at hfixed
  change (v, blackSideIndexOfStrandSlot
      (fkMedialVertexParity v) (pairing v) side) =
    (w, blackSideIndexOfStrandSlot
      (fkMedialVertexParity w) (pairing w) side') at hfixed
  have hv : v = w := congrArg Prod.fst hfixed
  subst w
  apply Prod.ext
  · rfl
  · have hs := congrArg Prod.snd hfixed
    cases hp : pairing v <;> cases hvp : fkMedialVertexParity v <;>
      cases side <;> cases side' <;>
      simp [blackSideIndexOfStrandSlot, hp, hvp] at hs ⊢

@[simp] theorem blackDartOfStrandSlot_strandSlotOfBlackDart
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T) :
    blackDartOfStrandSlot pairing (d.1.1,
      strandSlotOfBlackDart pairing d) = d := by
  apply (fkMedialBlackDartEquivVertexBool T).injective
  simp only [blackDartOfStrandSlot, Equiv.apply_symm_apply]
  rcases d with ⟨⟨v, side⟩, hd⟩
  cases side <;> cases hp : pairing v <;>
    cases hv : fkMedialVertexParity v <;>
    simp [strandSlotOfBlackDart,
      blackSideIndexOfStrandSlot, fkMedialBlackDartEquivVertexBool,
      fkMedialBlackDart0, fkMedialBlackDart1,
      fkMedialCheckerColor, fkMedialSideVertical, hp, hv] at hd ⊢


theorem blackBoundary_alignedSlot_first_step
    {T : EvenTorus} (pairingP pairingQ : FKMedialLoopPairing T)
    (v : T.Vertex) (localP localQ branch : Bool) (d : Fin 4)
    (hP : pairingP v = localP) (hQ : pairingQ v = localQ) :
    fkMedialBlackBoundaryPerm pairingP
        (blackDartOfStrandSlot pairingP
          (v, if branch then !strandSlot localP d else strandSlot localP d)) =
      fkMedialBlackBoundaryPerm pairingQ
        (blackDartOfStrandSlot pairingQ
          (v, if branch then
            !boundaryAlignedSlotQRaw (fkMedialVertexParity v)
              localP localQ d
          else boundaryAlignedSlotQRaw (fkMedialVertexParity v)
              localP localQ d)) := by
  apply Subtype.ext
  rw [fkMedialBlackBoundaryPerm_val, fkMedialBlackBoundaryPerm_val]
  cases localP <;> cases localQ <;> cases branch <;>
    cases hv : fkMedialVertexParity v <;> fin_cases d <;>
    simp [blackDartOfStrandSlot, blackSideIndexOfStrandSlot,
      fkMedialBlackDartEquivVertexBool, fkMedialBlackDart0,
      fkMedialBlackDart1, boundaryAlignedSlotQRaw, strandSlot,
      sideVertical, localMate, fkMedialLocalMate, hP, hQ, hv]

theorem blackBoundary_eq_of_pairing_eq_at
    {T : EvenTorus} (pairingP pairingQ : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T)
    (hlocal : pairingP d.1.1 = pairingQ d.1.1) :
    fkMedialBlackBoundaryPerm pairingP d =
      fkMedialBlackBoundaryPerm pairingQ d := by
  apply Subtype.ext
  rw [fkMedialBlackBoundaryPerm_val, fkMedialBlackBoundaryPerm_val]
  rcases d with ⟨⟨v, side⟩, hd⟩
  cases side <;> simp [fkMedialLocalMate, hlocal]


theorem exists_boundaryAligned_localC_defect :
    exists p q : SixVertexLocalIncomingPattern,
      p.Ice /\ q.Ice /\
      (sixVertexLocalDisagreementSides p q).card = 2 /\
      compatible false p /\ compatible true q /\
      p (2 : Fin 4) != q (2 : Fin 4) /\
      p (localMate true (localMate false (2 : Fin 4))) !=
        q (localMate true (localMate false (2 : Fin 4))) /\
      exchangedLocalCIndicator (strandSlot false (2 : Fin 4))
          (boundaryAlignedSlotQRaw false false true (2 : Fin 4)) p q !=
        localCIndicator p + localCIndicator q := by
  decide


theorem localCIndicator_exchange_boundary_aligned_exact
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity : Bool) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hcompatibleP : compatible pairingP p)
    (hcompatibleQ : compatible pairingQ q)
    (hd : p d != q d)
    (hpartner : p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d))) :
    exchangedLocalCIndicator (strandSlot pairingP d)
        (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q =
      localCIndicator p + localCIndicator q +
        if (pairingP != pairingQ) &&
            (vertexParity != sideVertical d) then 2 else 0 := by
  unfold boundaryAlignedSlotQRaw
    compatible exchangedLocalCIndicator exchangeLocalSlots
    localCIndicator horizontalSlot strandSlot sideVertical localMate at *
  cases pairingP <;> cases pairingQ <;> cases vertexParity <;> fin_cases d
  all_goals decide +revert

set_option maxHeartbeats 1000000 in


theorem localCIndicator_exchange_boundary_aligned_mask_exact
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity select0 select1 : Bool) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hcompatibleP : compatible pairingP p)
    (hcompatibleQ : compatible pairingQ q)
    (hd : p d != q d)
    (hpartner : p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d))) :
    exchangedLocalAlignedMaskCIndicator select0 select1
        (strandSlot pairingP d)
        (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q =
      localCIndicator p + localCIndicator q +
        if (select0 != select1) && (pairingP != pairingQ) &&
            (vertexParity != sideVertical d) then 2 else 0 := by
  unfold boundaryAlignedSlotQRaw compatible
    exchangedLocalAlignedMaskCIndicator exchangeLocalAlignedMask
    localCIndicator horizontalSlot strandSlot sideVertical localMate at *
  cases pairingP <;> cases pairingQ <;> cases vertexParity <;>
    cases select0 <;> cases select1 <;> fin_cases d
  all_goals decide +revert

theorem localCIndicator_le_exchange_boundary_aligned_mask
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity select0 select1 : Bool) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hcompatibleP : compatible pairingP p)
    (hcompatibleQ : compatible pairingQ q)
    (hd : p d != q d)
    (hpartner : p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d))) :
    localCIndicator p + localCIndicator q <=
      exchangedLocalAlignedMaskCIndicator select0 select1
        (strandSlot pairingP d)
        (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q := by
  rw [localCIndicator_exchange_boundary_aligned_mask_exact p q pairingP
    pairingQ vertexParity select0 select1 d hp hq hdegree hcompatibleP
    hcompatibleQ hd hpartner]
  exact Nat.le_add_right _ _

theorem localCIndicator_le_exchange_boundary_aligned
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity : Bool) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hcompatibleP : compatible pairingP p)
    (hcompatibleQ : compatible pairingQ q)
    (hd : p d != q d)
    (hpartner : p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d))) :
    localCIndicator p + localCIndicator q <=
      exchangedLocalCIndicator (strandSlot pairingP d)
        (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q := by
  rw [localCIndicator_exchange_boundary_aligned_exact p q pairingP pairingQ
    vertexParity d hp hq hdegree hcompatibleP hcompatibleQ hd hpartner]
  exact Nat.le_add_right _ _

theorem canonicalAlignedExitRetie_nondecreases_localC
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4)
    (vertexParity : Bool)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hd : p d != q d) :
    let retie := canonicalAlignedExitRetie p q d hp hq hdegree hd
    localCIndicator p + localCIndicator q <=
      exchangedLocalCIndicator retie.slotP
        (boundaryAlignedSlotQ vertexParity retie) p q := by
  dsimp only [AlignedExitRetie.slotP, boundaryAlignedSlotQ]
  apply localCIndicator_le_exchange_boundary_aligned p q
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).pairingP
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).pairingQ
    vertexParity d hp hq hdegree
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).compatibleP
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).compatibleQ hd
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).partnerDisagrees

theorem canonicalAlignedExitRetie_preserves_localC
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hd : p d != q d) :
    let retie := canonicalAlignedExitRetie p q d hp hq hdegree hd
    exchangedLocalCIndicator retie.slotP retie.slotQ p q =
      localCIndicator p + localCIndicator q := by
  dsimp only [AlignedExitRetie.slotP, AlignedExitRetie.slotQ,
    AlignedExitRetie.partnerSide]
  apply localCIndicator_exchange_aligned_exit p q
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).pairingP
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).pairingQ d
    hp hq hdegree
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).compatibleP
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).compatibleQ hd
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).partnerDisagrees

end ScratchLocalRetieC
