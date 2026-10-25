/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part31
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotRoute.Part5


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexDegreeTwoAlignedColoredSource_arrows
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (layer : Bool) :
    (sixVertexDegreeTwoAlignedColoredSource
      homega heta hdegree layer).arrows = if layer then eta else omega := by
  cases layer <;> exact SixVertexCompatibleLoopPairing.toColored_arrows _

theorem sixVertexDegreeTwoAlignedColoredSource_slotColor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (v : T.Vertex) (slot : Bool) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, v, slot) =
      (fkMedialVertexParity v ^^
        horizontalSlot
          (sixVertexLocalIncomingPattern (if layer then eta else omega) v)
          slot) := by
  cases layer <;> cases slot <;>
    simp [sixVertexDegreeTwoAlignedColoredSource,
      fkColoredLayeredSlotColor, SixVertexCompatibleLoopPairing.toColored,
      fkMedialCheckerColor, fkMedialSideVertical, horizontalSlot,
      sixVertexLocalIncomingPattern, fkMedialDartIncoming,
      fkLoopWestIncoming, fkLoopEastIncoming]


theorem sixVertexDegreeTwoAlignedColoredSource_doubledDart_color
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree layer).color
        (doubledAlignedBlackDart homega heta hdegree layer x).1) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x) := by
  cases layer
  · rw [FKColoredLoopPairing.color_blackDart_eq_slotColor]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (congrArg (fun slot : T.Vertex × Bool => (false, slot))
        (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
          (alignedRoutingLoopPairing homega heta hdegree false)
          (doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree false x)))
  · rw [FKColoredLoopPairing.color_blackDart_eq_slotColor]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (congrArg (fun slot : T.Vertex × Bool => (true, slot))
        (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
          (alignedRoutingLoopPairing homega heta hdegree true)
          (doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree true x)))


theorem sixVertexDegreeTwoAlignedColoredSource_falseDart_color
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
        (doubledAlignedBlackDart homega heta hdegree false x).1) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (false, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x) := by
  rw [FKColoredLoopPairing.color_blackDart_eq_slotColor]
  exact congrArg
    (fkColoredLayeredSlotColor
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
    (congrArg (fun slot : T.Vertex × Bool => (false, slot))
      (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
        (alignedRoutingLoopPairing homega heta hdegree false)
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x)))


theorem sixVertexDegreeTwoAlignedColoredSource_falseDart_true_color
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    let retie := orientedDartAlignedRetie homega heta hdegree x.1
    ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree true).color
        (doubledAlignedBlackDart homega heta hdegree false x).1) =
      if retie.pairingP = retie.pairingQ then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (true, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree true x)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (true, doubledAlignedVertex (doubledAlignedBranchSwap x),
            doubledAlignedSlot homega heta hdegree true
              (doubledAlignedBranchSwap x)) := by
  let retie := orientedDartAlignedRetie homega heta hdegree x.1
  change ((sixVertexDegreeTwoAlignedColoredSource
      homega heta hdegree true).color
        (doubledAlignedBlackDart homega heta hdegree false x).1) =
    if retie.pairingP = retie.pairingQ then
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree true x)
    else
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex (doubledAlignedBranchSwap x),
          doubledAlignedSlot homega heta hdegree true
            (doubledAlignedBranchSwap x))
  by_cases heq : retie.pairingP = retie.pairingQ
  · rw [if_pos heq]
    have hdart := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree x
    dsimp only at hdart
    rw [if_pos heq] at hdart
    rw [← hdart, FKColoredLoopPairing.color_blackDart_eq_slotColor]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (congrArg (fun slot : T.Vertex × Bool => (true, slot))
        (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
          (alignedRoutingLoopPairing homega heta hdegree true)
          (doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree true x)))
  · rw [if_neg heq]
    have hdart := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree (doubledAlignedBranchSwap x)
    simp only [doubledAlignedBranchSwap_fst,
      doubledAlignedBranchSwap_self] at hdart
    rw [if_neg heq] at hdart
    rw [← hdart, FKColoredLoopPairing.color_blackDart_eq_slotColor]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (congrArg (fun slot : T.Vertex × Bool => (true, slot))
        (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
          (alignedRoutingLoopPairing homega heta hdegree true)
          (doubledAlignedVertex (doubledAlignedBranchSwap x),
            doubledAlignedSlot homega heta hdegree true
              (doubledAlignedBranchSwap x))))


theorem FKColoredLoopPairing.color_blackBoundaryPerm
    {T : EvenTorus} (source : FKColoredLoopPairing T)
    (dart : FKMedialBlackDart T) :
    source.color (fkMedialBlackBoundaryPerm source.pairing dart).1 =
      source.color dart.1 := by
  exact (source.color_bondMate
    (fkMedialLocalMate source.pairing dart.1)).trans
      (source.color_localMate dart.1)


theorem FKColoredLoopPairing.color_blackBoundaryPerm_pow
    {T : EvenTorus} (source : FKColoredLoopPairing T)
    (dart : FKMedialBlackDart T) (k : Nat) :
    source.color ((fkMedialBlackBoundaryPerm source.pairing ^ k) dart).1 =
      source.color dart.1 := by
  induction k generalizing dart with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, Equiv.Perm.mul_apply]
      exact (ih (fkMedialBlackBoundaryPerm source.pairing dart)).trans
        (source.color_blackBoundaryPerm dart)


theorem sixVertexDegreeTwoAlignedColoredSource_boundaryPower_color
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta) (k : Nat) :
    ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree layer).color
        ((alignedBoundaryPerm homega heta hdegree layer ^ k)
          (doubledAlignedBlackDart homega heta hdegree layer x)).1) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x) := by
  have hpower := FKColoredLoopPairing.color_blackBoundaryPerm_pow
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree layer)
    (doubledAlignedBlackDart homega heta hdegree layer x) k
  have hpairing :
      (sixVertexDegreeTwoAlignedColoredSource
        homega heta hdegree layer).pairing =
        alignedRoutingLoopPairing homega heta hdegree layer := by
    cases layer <;> rfl
  rw [hpairing] at hpower
  change ((sixVertexDegreeTwoAlignedColoredSource
      homega heta hdegree layer).color
        ((alignedBoundaryPerm homega heta hdegree layer ^ k)
          (doubledAlignedBlackDart homega heta hdegree layer x)).1) =
    (sixVertexDegreeTwoAlignedColoredSource
      homega heta hdegree layer).color
        (doubledAlignedBlackDart homega heta hdegree layer x).1 at hpower
  rw [hpower, FKColoredLoopPairing.color_blackDart_eq_slotColor]
  rw [hpairing]
  exact congrArg
    (fkColoredLayeredSlotColor
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
    (congrArg (fun slot : T.Vertex × Bool => (layer, slot))
      (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
        (alignedRoutingLoopPairing homega heta hdegree layer)
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x)))


theorem sixVertexDegreeTwoAlignedColoredSource_boundarySegment_slotColor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta)
    (dart : FKMedialBlackDart T) (k : Nat)
    (hk : k < finiteFirstReturnTime
      (alignedBoundaryPerm homega heta hdegree false)
      (activeBlackDart (omega := omega) (eta := eta))
      (doubledAlignedBlackDartEquiv homega heta hdegree false x))
    (hpow : (alignedBoundaryPerm homega heta hdegree false ^ k)
      (doubledAlignedBlackDart homega heta hdegree false x) = dart) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x) := by
  classical
  cases layer
  · rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false,
      ← hpow]
    let powered := (alignedBoundaryPerm homega heta hdegree false ^ k)
      (doubledAlignedBlackDart homega heta hdegree false x)
    have hcoordinate := FKColoredLoopPairing.color_blackDart_eq_slotColor
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      false powered
    exact hcoordinate.symm.trans
      (sixVertexDegreeTwoAlignedColoredSource_boundaryPower_color
        homega heta hdegree false x k)
  · have hswap := alignedBlackDartLayerSwap_power
      homega heta hdegree x k hk
    rw [hpow] at hswap
    rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true,
      hswap]
    let powered := (alignedBoundaryPerm homega heta hdegree true ^ k)
      (doubledAlignedBlackDart homega heta hdegree true x)
    have hcoordinate := FKColoredLoopPairing.color_blackDart_eq_slotColor
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      true powered
    exact hcoordinate.symm.trans
      (sixVertexDegreeTwoAlignedColoredSource_boundaryPower_color
        homega heta hdegree true x k)


theorem sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_false
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (false, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (false,
          doubledAlignedVertex
            (doubledAlignedFirstReturnPerm homega heta hdegree x),
          doubledAlignedSlot homega heta hdegree false
            (doubledAlignedFirstReturnPerm homega heta hdegree x)) := by
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x
  let k := finiteFirstReturnTime
    (alignedBoundaryPerm homega heta hdegree false)
    (activeBlackDart (omega := omega) (eta := eta))
    (doubledAlignedBlackDartEquiv homega heta hdegree false x)
  have harrival := congrArg Subtype.val
    (doubledAlignedFirstReturnPerm_false_arrival
      homega heta hdegree x)
  change doubledAlignedBlackDart homega heta hdegree false y =
    (alignedBoundaryPerm homega heta hdegree false ^ k)
      (doubledAlignedBlackDart homega heta hdegree false x) at harrival
  have hpower :=
    sixVertexDegreeTwoAlignedColoredSource_boundaryPower_color
      homega heta hdegree false x k
  rw [← harrival] at hpower
  have hy := sixVertexDegreeTwoAlignedColoredSource_falseDart_color
    homega heta hdegree y
  exact hpower.symm.trans hy


theorem sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_true
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    let y := doubledAlignedFirstReturnPerm homega heta hdegree x
    let retie := orientedDartAlignedRetie homega heta hdegree y.1
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree true x) =
      if retie.pairingP = retie.pairingQ then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (true, doubledAlignedVertex y,
            doubledAlignedSlot homega heta hdegree true y)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (true, doubledAlignedVertex (doubledAlignedBranchSwap y),
            doubledAlignedSlot homega heta hdegree true
              (doubledAlignedBranchSwap y)) := by
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x
  let retie := orientedDartAlignedRetie homega heta hdegree y.1
  let k := finiteFirstReturnTime
    (alignedBoundaryPerm homega heta hdegree true)
    (activeBlackDart (omega := omega) (eta := eta))
    (doubledAlignedBlackDartEquiv homega heta hdegree true x)
  have harrival := doubledAlignedFirstReturnPerm_true_common_arrival
    homega heta hdegree x
  change (alignedBoundaryPerm homega heta hdegree true ^ k)
      (doubledAlignedBlackDart homega heta hdegree true x) =
    doubledAlignedBlackDart homega heta hdegree false y at harrival
  have hpower :=
    sixVertexDegreeTwoAlignedColoredSource_boundaryPower_color
      homega heta hdegree true x k
  rw [harrival] at hpower
  have hy := sixVertexDegreeTwoAlignedColoredSource_falseDart_true_color
    homega heta hdegree y
  change ((sixVertexDegreeTwoAlignedColoredSource
      homega heta hdegree true).color
        (doubledAlignedBlackDart homega heta hdegree false y).1) =
    (if retie.pairingP = retie.pairingQ then
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex y,
          doubledAlignedSlot homega heta hdegree true y)
    else
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex (doubledAlignedBranchSwap y),
          doubledAlignedSlot homega heta hdegree true
            (doubledAlignedBranchSwap y))) at hy
  exact hpower.symm.trans hy


theorem sixVertexDegreeTwoAlignedColoredSource_inactive_dart_color_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : FKMedialBlackDart T)
    (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) dart)) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (false, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree false dart) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree true dart) := by
  have hzero : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega dart.1.1)
      (sixVertexLocalIncomingPattern eta dart.1.1)).card = 0 := by
    rcases hdegree dart.1.1 with hzero | htwo
    · exact hzero
    · exact False.elim (hinactive htwo)
  have hpatterns : sixVertexLocalIncomingPattern eta dart.1.1 =
      sixVertexLocalIncomingPattern omega dart.1.1 :=
    (localIncomingPattern_eq_of_disagreement_card_zero _ _ hzero).symm
  have hpairing := alignedRoutingPairing_eq_layers_at_inactive
    homega heta hdegree dart.1.1 hzero
  change alignedRoutingLoopPairing homega heta hdegree false dart.1.1 =
    alignedRoutingLoopPairing homega heta hdegree true dart.1.1 at hpairing
  rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false,
    sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true,
    alignedBlackDartLayerSwap_inactive homega heta hdegree dart hinactive,
    sixVertexDegreeTwoAlignedColoredSource_slotColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor]
  simp only [Bool.false_eq_true, if_false, if_true,
    fkColoredBlackDartStrandSlotEquiv_apply,
    fkColoredBlackDartStrandSlot]
  rw [hpatterns, hpairing]


theorem sixVertexDegreeTwoAlignedColoredSource_activeSlot_bne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    let retie := orientedDartAlignedRetie homega heta hdegree x.1
    (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (false, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x) !=
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree true x)) =
      if x.2 then
        (retie.pairingP != retie.pairingQ) &&
          (fkMedialVertexParity (doubledAlignedVertex x) !=
            sideVertical x.1.1.1.2)
      else
        (retie.pairingP == retie.pairingQ) ||
          (fkMedialVertexParity (doubledAlignedVertex x) !=
            sideVertical x.1.1.1.2) := by
  rcases x with ⟨d, branch⟩
  let p := sixVertexLocalIncomingPattern omega d.1.1.1
  let q := sixVertexLocalIncomingPattern eta d.1.1.1
  let retie := orientedDartAlignedRetie homega heta hdegree d
  rw [sixVertexDegreeTwoAlignedColoredSource_slotColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor]
  simp only [Bool.false_eq_true, if_false, if_true]
  change
    ((fkMedialVertexParity d.1.1.1 ^^
          horizontalSlot p
            (if branch then !strandSlot retie.pairingP d.1.1.2
              else strandSlot retie.pairingP d.1.1.2)) !=
      (fkMedialVertexParity d.1.1.1 ^^
          horizontalSlot q
            (if branch then
              !boundaryAlignedSlotQRaw (fkMedialVertexParity d.1.1.1)
                retie.pairingP retie.pairingQ d.1.1.2
            else boundaryAlignedSlotQRaw
              (fkMedialVertexParity d.1.1.1)
                retie.pairingP retie.pairingQ d.1.1.2))) =
      if branch then
        (retie.pairingP != retie.pairingQ) &&
          (fkMedialVertexParity d.1.1.1 != sideVertical d.1.1.2)
      else
        (retie.pairingP == retie.pairingQ) ||
          (fkMedialVertexParity d.1.1.1 != sideVertical d.1.1.2)
  cases branch
  · exact boundaryAlignedSlotColor_bne p q retie.pairingP retie.pairingQ
      (fkMedialVertexParity d.1.1.1) d.1.1.2
      (sixVertexLocalIncomingPattern_ice omega homega d.1.1.1)
      (sixVertexLocalIncomingPattern_ice eta heta d.1.1.1)
      (sixVertexDisagreementDart_local_card_eq_two hdegree d.1)
      retie.compatibleP retie.compatibleQ
      (by
        have hd := sixVertexDisagreementDart_side_mem d.1
        rw [mem_sixVertexLocalDisagreementSides] at hd
        exact bne_iff_ne.mpr hd)
      retie.partnerDisagrees
  · simpa using boundaryAlignedComplementSlotColor_bne p q
      retie.pairingP retie.pairingQ
      (fkMedialVertexParity d.1.1.1) d.1.1.2
      (sixVertexLocalIncomingPattern_ice omega homega d.1.1.1)
      (sixVertexLocalIncomingPattern_ice eta heta d.1.1.1)
      (sixVertexDisagreementDart_local_card_eq_two hdegree d.1)
      retie.compatibleP retie.compatibleQ
      (by
        have hd := sixVertexDisagreementDart_side_mem d.1
        rw [mem_sixVertexLocalDisagreementSides] at hd
        exact bne_iff_ne.mpr hd)
      retie.partnerDisagrees


theorem sixVertexDegreeTwoAlignedColoredSource_true_branchSwap_bne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta)
    (hne : (orientedDartAlignedRetie
      homega heta hdegree x.1).pairingP !=
        (orientedDartAlignedRetie
          homega heta hdegree x.1).pairingQ) :
    (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree true x) !=
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex (doubledAlignedBranchSwap x),
          doubledAlignedSlot homega heta hdegree true
            (doubledAlignedBranchSwap x))) = true := by
  rcases x with ⟨d, branch⟩
  let p := sixVertexLocalIncomingPattern omega d.1.1.1
  let q := sixVertexLocalIncomingPattern eta d.1.1.1
  let retie := orientedDartAlignedRetie homega heta hdegree d
  rw [sixVertexDegreeTwoAlignedColoredSource_slotColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor]
  simp only [if_true,
    doubledAlignedVertex, doubledAlignedBranchSwap,
    doubledAlignedSlot, Bool.not_eq_eq_eq_not]
  simp only [orientedDartBoundaryAlignedSlot, boundaryAlignedSlotQ, if_true]
  have hlocal := boundaryAlignedSlotQRaw_complement_color_bne_of_pairing_ne
    p q retie.pairingP retie.pairingQ
    (fkMedialVertexParity d.1.1.1) d.1.1.2
    (sixVertexLocalIncomingPattern_ice omega homega d.1.1.1)
    (sixVertexLocalIncomingPattern_ice eta heta d.1.1.1)
    (sixVertexDisagreementDart_local_card_eq_two hdegree d.1)
    retie.compatibleP retie.compatibleQ
    (by
      have hd := sixVertexDisagreementDart_side_mem d.1
      rw [mem_sixVertexLocalDisagreementSides] at hd
      exact bne_iff_ne.mpr hd)
    retie.partnerDisagrees hne
  cases branch
  · simpa [p, q, retie] using hlocal
  · simpa [p, q, retie, bne_comm] using hlocal


theorem sixVertexDegreeTwoAlignedColoredSource_true_branchSwap_bne_of_false_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta)
    (hfalse :
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (false, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree false x) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (false, doubledAlignedVertex (doubledAlignedBranchSwap x),
            doubledAlignedSlot homega heta hdegree false
              (doubledAlignedBranchSwap x))) :
    (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree true x) !=
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex (doubledAlignedBranchSwap x),
          doubledAlignedSlot homega heta hdegree true
            (doubledAlignedBranchSwap x))) = true := by
  let retie := orientedDartAlignedRetie homega heta hdegree x.1
  by_cases hpairing : retie.pairingP = retie.pairingQ
  · have hcrossX := sixVertexDegreeTwoAlignedColoredSource_activeSlot_bne
      homega heta hdegree x
    have hcrossSwap := sixVertexDegreeTwoAlignedColoredSource_activeSlot_bne
      homega heta hdegree (doubledAlignedBranchSwap x)
    have hswapBranch : (doubledAlignedBranchSwap x).2 = !x.2 := rfl
    by_cases hbranch : x.2 = true
    · have hsameX :
          fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (false, doubledAlignedVertex x,
                doubledAlignedSlot homega heta hdegree false x) =
            fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (true, doubledAlignedVertex x,
                doubledAlignedSlot homega heta hdegree true x) := by
        simpa [retie, hpairing, hbranch] using hcrossX
      have hneSwap :
          fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (false, doubledAlignedVertex (doubledAlignedBranchSwap x),
                doubledAlignedSlot homega heta hdegree false
                  (doubledAlignedBranchSwap x)) ≠
            fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (true, doubledAlignedVertex (doubledAlignedBranchSwap x),
                doubledAlignedSlot homega heta hdegree true
                  (doubledAlignedBranchSwap x)) := by
        simpa [retie, hpairing, hbranch, hswapBranch] using hcrossSwap
      apply bne_iff_ne.mpr
      intro heq
      apply hneSwap
      exact hfalse.symm.trans (hsameX.trans heq)
    · have hneX :
          fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (false, doubledAlignedVertex x,
                doubledAlignedSlot homega heta hdegree false x) ≠
            fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (true, doubledAlignedVertex x,
                doubledAlignedSlot homega heta hdegree true x) := by
        simpa [retie, hpairing, hbranch] using hcrossX
      have hsameSwap :
          fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (false, doubledAlignedVertex (doubledAlignedBranchSwap x),
                doubledAlignedSlot homega heta hdegree false
                  (doubledAlignedBranchSwap x)) =
            fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (true, doubledAlignedVertex (doubledAlignedBranchSwap x),
                doubledAlignedSlot homega heta hdegree true
                  (doubledAlignedBranchSwap x)) := by
        simpa [retie, hpairing, hbranch, hswapBranch] using hcrossSwap
      apply bne_iff_ne.mpr
      intro heq
      apply hneX
      exact hfalse.trans (hsameSwap.trans heq.symm)
  · exact sixVertexDegreeTwoAlignedColoredSource_true_branchSwap_bne
      homega heta hdegree x (bne_iff_ne.mpr hpairing)

theorem sixVertexDegreeTwoAlignedTransportedColor_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoAlignedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x)) =
      if _hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates
          homega heta hdegree middle homegaSector hetaSector hmiddle then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (!layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree (!layer) x)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x) := by
  classical
  by_cases hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates
      homega heta hdegree middle homegaSector hetaSector hmiddle
  · rw [dif_pos hx]
    let i := sixVertexDegreeTwoAlignedSelectedStateFinIndex
      homega heta hdegree middle homegaSector hetaSector hmiddle x hx
    rw [← sixVertexDegreeTwoAlignedBoundaryFinKey_selectedState
        homega heta hdegree middle homegaSector hetaSector hmiddle x hx layer]
    rw [fkIndexedOccurrenceSlotEquiv_apply_key]
    rw [sixVertexDegreeTwoAlignedBoundaryFinKey_selectedState]
  · rw [dif_neg hx]
    apply congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
    apply fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
    intro hexists
    apply hx
    exact (sixVertexDegreeTwoAlignedBoundaryFinKey_exists_iff
      homega heta hdegree middle homegaSector hetaSector hmiddle layer x).mp
        hexists


end
end StatMech.FrontierD
