import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part26
open StatMech.FrontierD ScratchLocalRetieC ScratchLocalRetieC.FourByTwoBondAudit


/--
[localPreferredPairing_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma localPreferredPairing_compatible_eq
  {p : SixVertexLocalIncomingPattern}
-- given
  (hp : p.Ice) :
-- imply
  compatible (localPreferredPairing p) p := by
-- proof
  apply ScratchLocalRetieC.localPreferredPairing_compatible p hp

/--
[compatible_iff_fkLoopPairingCompatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma compatible_iff_fkLoopPairingCompatible_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {v : T.Vertex}
  {pairing : Bool} :
-- imply
  compatible pairing (sixVertexLocalIncomingPattern omega v) <-> fkLoopPairingCompatible pairing omega v := by
-- proof
  apply ScratchLocalRetieC.compatible_iff_fkLoopPairingCompatible omega v pairing

/--
[localCIndicator_eq_ite_isCType](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma localCIndicator_eq_ite_isCType_eq
  {p : SixVertexLocalIncomingPattern} :
-- imply
  localCIndicator p = if p.IsCType then 1 else 0 := by
-- proof
  apply ScratchLocalRetieC.localCIndicator_eq_ite_isCType p

/--
[localCIndicator_localIncomingPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma localCIndicator_localIncomingPattern_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  localCIndicator (sixVertexLocalIncomingPattern omega v) = if omega.IsCType v then 1 else 0 := by
-- proof
  apply ScratchLocalRetieC.localCIndicator_localIncomingPattern omega v

/--
[sixVertexPairTotalC_mono_of_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma sixVertexPairTotalC_mono_of_local_eq
  {T : EvenTorus}
  {omega eta omega' eta' : SixVertexArrows T}
-- given
  (hlocal : forall v, localCIndicator (sixVertexLocalIncomingPattern omega v) + localCIndicator (sixVertexLocalIncomingPattern eta v) <= localCIndicator (sixVertexLocalIncomingPattern omega' v) + localCIndicator (sixVertexLocalIncomingPattern eta' v)) :
-- imply
  sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta <= sixVertexTorusCTypeCount omega' + sixVertexTorusCTypeCount eta' := by
-- proof
  apply ScratchLocalRetieC.sixVertexPairTotalC_mono_of_local omega eta omega' eta' hlocal

/--
[localIncomingPattern_arrowsOfIncomingPatterns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma localIncomingPattern_arrowsOfIncomingPatterns_eq
  {T : EvenTorus}
  {v : T.Vertex}
-- given
  (patterns : T.Vertex -> SixVertexLocalIncomingPattern)
  (hwest : forall v, patterns v 0 = !patterns (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) 1)
  (hsouth : forall v, patterns v 2 = !patterns (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) 3) :
-- imply
  sixVertexLocalIncomingPattern (arrowsOfIncomingPatterns patterns) v = patterns v := by
-- proof
  apply ScratchLocalRetieC.localIncomingPattern_arrowsOfIncomingPatterns patterns hwest hsouth v

/--
[arrowsOfIncomingPatterns_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma arrowsOfIncomingPatterns_ice_eq
  {T : EvenTorus}
-- given
  (patterns : T.Vertex -> SixVertexLocalIncomingPattern)
  (hwest : forall v, patterns v 0 = !patterns (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) 1)
  (hsouth : forall v, patterns v 2 = !patterns (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) 3)
  (hice : forall v, (patterns v).Ice) :
-- imply
  (arrowsOfIncomingPatterns patterns).IceRule := by
-- proof
  apply ScratchLocalRetieC.arrowsOfIncomingPatterns_ice patterns hwest hsouth hice

/--
[localCIndicator_exchange_aligned_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma localCIndicator_exchange_aligned_exit_eq
  {p q : SixVertexLocalIncomingPattern}
  {pairingP pairingQ : Bool}
  {d : Fin 4}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
  (hcompatibleP : compatible pairingP p)
  (hcompatibleQ : compatible pairingQ q)
  (hd : p d != q d)
  (hpartner : p (localMate pairingQ (localMate pairingP d)) != q (localMate pairingQ (localMate pairingP d))) :
-- imply
  exchangedLocalCIndicator (strandSlot pairingP d) (strandSlot pairingQ (localMate pairingQ (localMate pairingP d))) p q = localCIndicator p + localCIndicator q := by
-- proof
  apply ScratchLocalRetieC.localCIndicator_exchange_aligned_exit p q pairingP pairingQ d hp hq hdegree hcompatibleP hcompatibleQ hd hpartner

/--
[exists_compatible_aligned_exit_pairings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma exists_compatible_aligned_exit_pairings_eq
  {p q : SixVertexLocalIncomingPattern}
  {d : Fin 4}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
  (hd : p d != q d) :
-- imply
  exists pairingP pairingQ : Bool, compatible pairingP p /\ compatible pairingQ q /\ p (localMate pairingQ (localMate pairingP d)) != q (localMate pairingQ (localMate pairingP d)) := by
-- proof
  apply ScratchLocalRetieC.exists_compatible_aligned_exit_pairings p q d hp hq hdegree hd

/--
[localMate_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma localMate_involutive_eq
  {pairing : Bool}
  {d : Fin 4} :
-- imply
  localMate pairing (localMate pairing d) = d := by
-- proof
  apply ScratchLocalRetieC.localMate_involutive pairing d

/--
[AlignedExitRetie.common_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma common_exit_eq
  {p q : SixVertexLocalIncomingPattern}
  {d : Fin 4}
  {retie : AlignedExitRetie p q d} :
-- imply
  localMate retie.pairingP d = localMate retie.pairingQ retie.partnerSide := by
-- proof
  apply ScratchLocalRetieC.AlignedExitRetie.common_exit retie

/--
[blackDartOfStrandSlot_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma blackDartOfStrandSlot_vertex_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {slot : T.Vertex × Bool} :
-- imply
  (blackDartOfStrandSlot pairing slot).1.1 = slot.1 := by
-- proof
  apply ScratchLocalRetieC.blackDartOfStrandSlot_vertex pairing slot

/--
[blackDartOfStrandSlot_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma blackDartOfStrandSlot_injective_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T} :
-- imply
  Function.Injective (blackDartOfStrandSlot pairing) := by
-- proof
  apply ScratchLocalRetieC.blackDartOfStrandSlot_injective pairing

/--
[blackDartOfStrandSlot_strandSlotOfBlackDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma blackDartOfStrandSlot_strandSlotOfBlackDart_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  blackDartOfStrandSlot pairing (d.1.1, strandSlotOfBlackDart pairing d) = d := by
-- proof
  apply ScratchLocalRetieC.blackDartOfStrandSlot_strandSlotOfBlackDart pairing d

/--
[blackBoundary_alignedSlot_first_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma blackBoundary_alignedSlot_first_step_eq
  {T : EvenTorus}
  {pairingP pairingQ : FKMedialLoopPairing T}
  {v : T.Vertex}
  {localP localQ branch : Bool}
  {d : Fin 4}
-- given
  (hP : pairingP v = localP)
  (hQ : pairingQ v = localQ) :
-- imply
  fkMedialBlackBoundaryPerm pairingP (blackDartOfStrandSlot pairingP (v, if branch then !strandSlot localP d else strandSlot localP d)) = fkMedialBlackBoundaryPerm pairingQ (blackDartOfStrandSlot pairingQ (v, if branch then !boundaryAlignedSlotQRaw (fkMedialVertexParity v) localP localQ d else boundaryAlignedSlotQRaw (fkMedialVertexParity v) localP localQ d)) := by
-- proof
  apply ScratchLocalRetieC.blackBoundary_alignedSlot_first_step pairingP pairingQ v localP localQ branch d hP hQ

/--
[blackBoundary_eq_of_pairing_eq_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma blackBoundary_eq_of_pairing_eq_at_eq
  {T : EvenTorus}
  {pairingP pairingQ : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T}
-- given
  (hlocal : pairingP d.1.1 = pairingQ d.1.1) :
-- imply
  fkMedialBlackBoundaryPerm pairingP d = fkMedialBlackBoundaryPerm pairingQ d := by
-- proof
  apply ScratchLocalRetieC.blackBoundary_eq_of_pairing_eq_at pairingP pairingQ d hlocal

/--
[exists_boundaryAligned_localC_defect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma exists_boundaryAligned_localC_defect_eq :
-- imply
  exists p q : SixVertexLocalIncomingPattern, p.Ice /\ q.Ice /\ (sixVertexLocalDisagreementSides p q).card = 2 /\ compatible false p /\ compatible true q /\ p (2 : Fin 4) != q (2 : Fin 4) /\ p (localMate true (localMate false (2 : Fin 4))) != q (localMate true (localMate false (2 : Fin 4))) /\ exchangedLocalCIndicator (strandSlot false (2 : Fin 4)) (boundaryAlignedSlotQRaw false false true (2 : Fin 4)) p q != localCIndicator p + localCIndicator q := by
-- proof
  apply ScratchLocalRetieC.exists_boundaryAligned_localC_defect

/--
[localCIndicator_exchange_boundary_aligned_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma localCIndicator_exchange_boundary_aligned_exact_eq
  {p q : SixVertexLocalIncomingPattern}
  {pairingP pairingQ vertexParity : Bool}
  {d : Fin 4}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
  (hcompatibleP : compatible pairingP p)
  (hcompatibleQ : compatible pairingQ q)
  (hd : p d != q d)
  (hpartner : p (localMate pairingQ (localMate pairingP d)) != q (localMate pairingQ (localMate pairingP d))) :
-- imply
  exchangedLocalCIndicator (strandSlot pairingP d) (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q = localCIndicator p + localCIndicator q + if (pairingP != pairingQ) && (vertexParity != sideVertical d) then 2 else 0 := by
-- proof
  apply ScratchLocalRetieC.localCIndicator_exchange_boundary_aligned_exact p q pairingP pairingQ vertexParity d hp hq hdegree hcompatibleP hcompatibleQ hd hpartner

/--
[localCIndicator_exchange_boundary_aligned_mask_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma localCIndicator_exchange_boundary_aligned_mask_exact_eq
  {p q : SixVertexLocalIncomingPattern}
  {pairingP pairingQ vertexParity select0 select1 : Bool}
  {d : Fin 4}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
  (hcompatibleP : compatible pairingP p)
  (hcompatibleQ : compatible pairingQ q)
  (hd : p d != q d)
  (hpartner : p (localMate pairingQ (localMate pairingP d)) != q (localMate pairingQ (localMate pairingP d))) :
-- imply
  exchangedLocalAlignedMaskCIndicator select0 select1 (strandSlot pairingP d) (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q = localCIndicator p + localCIndicator q + if (select0 != select1) && (pairingP != pairingQ) && (vertexParity != sideVertical d) then 2 else 0 := by
-- proof
  apply ScratchLocalRetieC.localCIndicator_exchange_boundary_aligned_mask_exact p q pairingP pairingQ vertexParity select0 select1 d hp hq hdegree hcompatibleP hcompatibleQ hd hpartner

/--
[localCIndicator_le_exchange_boundary_aligned_mask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma localCIndicator_le_exchange_boundary_aligned_mask_eq
  {p q : SixVertexLocalIncomingPattern}
  {pairingP pairingQ vertexParity select0 select1 : Bool}
  {d : Fin 4}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
  (hcompatibleP : compatible pairingP p)
  (hcompatibleQ : compatible pairingQ q)
  (hd : p d != q d)
  (hpartner : p (localMate pairingQ (localMate pairingP d)) != q (localMate pairingQ (localMate pairingP d))) :
-- imply
  localCIndicator p + localCIndicator q <= exchangedLocalAlignedMaskCIndicator select0 select1 (strandSlot pairingP d) (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q := by
-- proof
  apply ScratchLocalRetieC.localCIndicator_le_exchange_boundary_aligned_mask p q pairingP pairingQ vertexParity select0 select1 d hp hq hdegree hcompatibleP hcompatibleQ hd hpartner

/--
[localCIndicator_le_exchange_boundary_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma localCIndicator_le_exchange_boundary_aligned_eq
  {p q : SixVertexLocalIncomingPattern}
  {pairingP pairingQ vertexParity : Bool}
  {d : Fin 4}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
  (hcompatibleP : compatible pairingP p)
  (hcompatibleQ : compatible pairingQ q)
  (hd : p d != q d)
  (hpartner : p (localMate pairingQ (localMate pairingP d)) != q (localMate pairingQ (localMate pairingP d))) :
-- imply
  localCIndicator p + localCIndicator q <= exchangedLocalCIndicator (strandSlot pairingP d) (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q := by
-- proof
  apply ScratchLocalRetieC.localCIndicator_le_exchange_boundary_aligned p q pairingP pairingQ vertexParity d hp hq hdegree hcompatibleP hcompatibleQ hd hpartner

/--
[canonicalAlignedExitRetie_nondecreases_localC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma canonicalAlignedExitRetie_nondecreases_localC_eq
  {p q : SixVertexLocalIncomingPattern}
  {d : Fin 4}
  {vertexParity : Bool}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
  (hd : p d != q d) :
-- imply
  let retie := canonicalAlignedExitRetie p q d hp hq hdegree hd localCIndicator p + localCIndicator q <= exchangedLocalCIndicator retie.slotP (boundaryAlignedSlotQ vertexParity retie) p q := by
-- proof
  apply ScratchLocalRetieC.canonicalAlignedExitRetie_nondecreases_localC p q d vertexParity hp hq hdegree hd

/--
[canonicalAlignedExitRetie_preserves_localC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma canonicalAlignedExitRetie_preserves_localC_eq
  {p q : SixVertexLocalIncomingPattern}
  {d : Fin 4}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
  (hd : p d != q d) :
-- imply
  let retie := canonicalAlignedExitRetie p q d hp hq hdegree hd exchangedLocalCIndicator retie.slotP retie.slotQ p q = localCIndicator p + localCIndicator q := by
-- proof
  apply ScratchLocalRetieC.canonicalAlignedExitRetie_preserves_localC p q d hp hq hdegree hd

/--
[orientedDartAlignedRetie_preserves_localC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma orientedDartAlignedRetie_preserves_localC_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  let retie := orientedDartAlignedRetie homega heta hdegree d exchangedLocalCIndicator retie.slotP retie.slotQ (sixVertexLocalIncomingPattern omega d.1.1.1) (sixVertexLocalIncomingPattern eta d.1.1.1) = localCIndicator (sixVertexLocalIncomingPattern omega d.1.1.1) + localCIndicator (sixVertexLocalIncomingPattern eta d.1.1.1) := by
-- proof
  apply ScratchLocalRetieC.orientedDartAlignedRetie_preserves_localC homega heta hdegree d

/--
[orientedDartBoundaryAlignedRetie_nondecreases_localC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma orientedDartBoundaryAlignedRetie_nondecreases_localC_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  localCIndicator (sixVertexLocalIncomingPattern omega d.1.1.1) + localCIndicator (sixVertexLocalIncomingPattern eta d.1.1.1) <= exchangedLocalCIndicator (orientedDartBoundaryAlignedSlot homega heta hdegree false d) (orientedDartBoundaryAlignedSlot homega heta hdegree true d) (sixVertexLocalIncomingPattern omega d.1.1.1) (sixVertexLocalIncomingPattern eta d.1.1.1) := by
-- proof
  apply ScratchLocalRetieC.orientedDartBoundaryAlignedRetie_nondecreases_localC homega heta hdegree d

/--
[orientedDartBoundaryAlignedMask_nondecreases_localC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma orientedDartBoundaryAlignedMask_nondecreases_localC_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {select0 select1 : Bool}
  {d : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  localCIndicator (sixVertexLocalIncomingPattern omega d.1.1.1) + localCIndicator (sixVertexLocalIncomingPattern eta d.1.1.1) <= exchangedLocalAlignedMaskCIndicator select0 select1 (orientedDartBoundaryAlignedSlot homega heta hdegree false d) (orientedDartBoundaryAlignedSlot homega heta hdegree true d) (sixVertexLocalIncomingPattern omega d.1.1.1) (sixVertexLocalIncomingPattern eta d.1.1.1) := by
-- proof
  apply ScratchLocalRetieC.orientedDartBoundaryAlignedMask_nondecreases_localC homega heta hdegree select0 select1 d

/--
[orientedDisagreementDart_eq_of_vertex_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma orientedDisagreementDart_eq_of_vertex_eq_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d e : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hvertex : d.1.1.1 = e.1.1.1) :
-- imply
  d = e := by
-- proof
  apply ScratchLocalRetieC.orientedDisagreementDart_eq_of_vertex_eq homega heta hdegree d e hvertex

/--
[exists_incoming_disagreement_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma exists_incoming_disagreement_side_eq
  {p q : SixVertexLocalIncomingPattern}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hdegree : (sixVertexLocalDisagreementSides p q).card = 2) :
-- imply
  exists d : Fin 4, p d != q d /\ p d = true := by
-- proof
  apply ScratchLocalRetieC.exists_incoming_disagreement_side p q hp hq hdegree

/--
[alignedMaskedTarget_localIncomingPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedMaskedTarget_localIncomingPattern_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (select0 select1 : T.Vertex -> Bool)
  (hbond : AlignedMaskedBondConsistent homega heta hdegree select0 select1) :
-- imply
  sixVertexLocalIncomingPattern (alignedMaskedTarget homega heta hdegree select0 select1 layer) v = alignedMaskedLocalPattern homega heta hdegree select0 select1 layer v := by
-- proof
  apply ScratchLocalRetieC.alignedMaskedTarget_localIncomingPattern homega heta hdegree select0 select1 hbond layer v

/--
[sixVertexPairTotalC_mono_of_alignedLocalMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma sixVertexPairTotalC_mono_of_alignedLocalMask_eq
  {T : EvenTorus}
  {omega eta omega' eta' : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (select0 select1 : T.Vertex -> Bool)
  (hactive : forall (v : T.Vertex) (hv : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 2), let d := orientedDisagreementDartAtActiveVertex homega heta v hv (sixVertexLocalIncomingPattern omega' v, sixVertexLocalIncomingPattern eta' v) = exchangeLocalAlignedMask (select0 v) (select1 v) (orientedDartBoundaryAlignedSlot homega heta hdegree false d) (orientedDartBoundaryAlignedSlot homega heta hdegree true d) (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v))
  (hinactive : forall (v : T.Vertex) (hv : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 0), (sixVertexLocalIncomingPattern omega' v, sixVertexLocalIncomingPattern eta' v) = (sixVertexLocalIncomingPattern omega v, sixVertexLocalIncomingPattern eta v)) :
-- imply
  sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta <= sixVertexTorusCTypeCount omega' + sixVertexTorusCTypeCount eta' := by
-- proof
  apply ScratchLocalRetieC.sixVertexPairTotalC_mono_of_alignedLocalMask homega heta hdegree select0 select1 hactive hinactive

/--
[alignedMaskedTarget_totalC_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedMaskedTarget_totalC_mono_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (select0 select1 : T.Vertex -> Bool)
  (hbond : AlignedMaskedBondConsistent homega heta hdegree select0 select1) :
-- imply
  sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta <= sixVertexTorusCTypeCount (alignedMaskedTarget homega heta hdegree select0 select1 false) + sixVertexTorusCTypeCount (alignedMaskedTarget homega heta hdegree select0 select1 true) := by
-- proof
  apply ScratchLocalRetieC.alignedMaskedTarget_totalC_mono homega heta hdegree select0 select1 hbond

/--
[localIncomingPattern_eq_of_disagreement_card_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma localIncomingPattern_eq_of_disagreement_card_zero_eq
  {p q : SixVertexLocalIncomingPattern}
-- given
  (hzero : (sixVertexLocalDisagreementSides p q).card = 0) :
-- imply
  p = q := by
-- proof
  apply ScratchLocalRetieC.localIncomingPattern_eq_of_disagreement_card_zero p q hzero

/--
[alignedRoutingPairing_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedRoutingPairing_compatible_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  fkLoopPairingCompatible (alignedRoutingPairing homega heta hdegree layer v) (if layer then eta else omega) v := by
-- proof
  apply ScratchLocalRetieC.alignedRoutingPairing_compatible homega heta hdegree layer v

/--
[alignedRoutingPairing_eq_at_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedRoutingPairing_eq_at_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hactive : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 2) :
-- imply
  alignedRoutingPairing homega heta hdegree layer v = let d := orientedDisagreementDartAtActiveVertex homega heta v hactive let retie := orientedDartAlignedRetie homega heta hdegree d if layer then retie.pairingQ else retie.pairingP := by
-- proof
  apply ScratchLocalRetieC.alignedRoutingPairing_eq_at_active homega heta hdegree layer v hactive

/--
[alignedRoutingPairing_eq_layers_at_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedRoutingPairing_eq_layers_at_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hzero : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 0) :
-- imply
  alignedRoutingPairing homega heta hdegree false v = alignedRoutingPairing homega heta hdegree true v := by
-- proof
  apply ScratchLocalRetieC.alignedRoutingPairing_eq_layers_at_inactive homega heta hdegree v hzero

/--
[doubledAlignedBlackDart_first_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma doubledAlignedBlackDart_first_step_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  fkMedialBlackBoundaryPerm (alignedRoutingLoopPairing homega heta hdegree false) (doubledAlignedBlackDart homega heta hdegree false x) = fkMedialBlackBoundaryPerm (alignedRoutingLoopPairing homega heta hdegree true) (doubledAlignedBlackDart homega heta hdegree true x) := by
-- proof
  apply ScratchLocalRetieC.doubledAlignedBlackDart_first_step homega heta hdegree x

/--
[mem_range_doubledAlignedSlotEmbedding_iff_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma mem_range_doubledAlignedSlotEmbedding_iff_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {v : T.Vertex}
  {side : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (v, side) ∈ Set.range (doubledAlignedSlotEmbedding homega heta hdegree layer) ↔ (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 2 := by
-- proof
  apply ScratchLocalRetieC.mem_range_doubledAlignedSlotEmbedding_iff_active homega heta hdegree layer v side

/--
[doubledAlignedBlackDart_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma doubledAlignedBlackDart_injective_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  Function.Injective (doubledAlignedBlackDart homega heta hdegree layer) := by
-- proof
  apply ScratchLocalRetieC.doubledAlignedBlackDart_injective homega heta hdegree layer

/--
[doubledAlignedBlackDart_surjective_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma doubledAlignedBlackDart_surjective_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  Function.Surjective (fun x : DoubledAlignedState omega eta => (⟨doubledAlignedBlackDart homega heta hdegree layer x, by simpa [activeBlackDart, doubledAlignedBlackDart, doubledAlignedVertex] using sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1⟩ : {d : FKMedialBlackDart T // activeBlackDart (omega := omega) (eta := eta) d})) := by
-- proof
  apply ScratchLocalRetieC.doubledAlignedBlackDart_surjective_active homega heta hdegree layer

/--
[alignedFirstReturnTime_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedFirstReturnTime_eq_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  finiteFirstReturnTime (alignedBoundaryPerm homega heta hdegree false) (activeBlackDart (omega := omega) (eta := eta)) (doubledAlignedBlackDartEquiv homega heta hdegree false x) = finiteFirstReturnTime (alignedBoundaryPerm homega heta hdegree true) (activeBlackDart (omega := omega) (eta := eta)) (doubledAlignedBlackDartEquiv homega heta hdegree true x) := by
-- proof
  apply ScratchLocalRetieC.alignedFirstReturnTime_eq homega heta hdegree x

/--
[alignedFirstReturn_common_arrival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedFirstReturn_common_arrival_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (finiteFirstReturn (alignedBoundaryPerm homega heta hdegree false) (activeBlackDart (omega := omega) (eta := eta)) (doubledAlignedBlackDartEquiv homega heta hdegree false x)).1 = (finiteFirstReturn (alignedBoundaryPerm homega heta hdegree true) (activeBlackDart (omega := omega) (eta := eta)) (doubledAlignedBlackDartEquiv homega heta hdegree true x)).1 := by
-- proof
  apply ScratchLocalRetieC.alignedFirstReturn_common_arrival homega heta hdegree x

/--
[doubledAlignedBoundarySegments_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma doubledAlignedBoundarySegments_nodup_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {states : List (DoubledAlignedState omega eta)}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hstates : states.Nodup) :
-- imply
  (doubledAlignedBoundarySegments homega heta hdegree layer states).Nodup := by
-- proof
  apply ScratchLocalRetieC.doubledAlignedBoundarySegments_nodup homega heta hdegree layer states hstates

/--
[mem_doubledAlignedBoundarySegments_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma mem_doubledAlignedBoundarySegments_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {states : List (DoubledAlignedState omega eta)}
  {d : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  d ∈ doubledAlignedBoundarySegments homega heta hdegree layer states ↔ ∃ x ∈ states, ∃ k : Nat, k < finiteFirstReturnTime (alignedBoundaryPerm homega heta hdegree layer) (activeBlackDart (omega := omega) (eta := eta)) (doubledAlignedBlackDartEquiv homega heta hdegree layer x) ∧ (alignedBoundaryPerm homega heta hdegree layer ^ k) (doubledAlignedBlackDart homega heta hdegree layer x) = d := by
-- proof
  apply ScratchLocalRetieC.mem_doubledAlignedBoundarySegments_iff homega heta hdegree layer states d

/--
[doubledAlignedBlackDart_mem_boundarySegments_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma doubledAlignedBlackDart_mem_boundarySegments_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {states : List (DoubledAlignedState omega eta)}
  {y : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  doubledAlignedBlackDart homega heta hdegree layer y ∈ doubledAlignedBoundarySegments homega heta hdegree layer states ↔ y ∈ states := by
-- proof
  apply ScratchLocalRetieC.doubledAlignedBlackDart_mem_boundarySegments_iff homega heta hdegree layer states y

/--
[length_doubledAlignedBoundarySegments_eq_layers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma length_doubledAlignedBoundarySegments_eq_layers_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {states : List (DoubledAlignedState omega eta)}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (doubledAlignedBoundarySegments homega heta hdegree false states).length = (doubledAlignedBoundarySegments homega heta hdegree true states).length := by
-- proof
  apply ScratchLocalRetieC.length_doubledAlignedBoundarySegments_eq_layers homega heta hdegree states

/--
[alignedBlackDartLayerSwap_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedBlackDartLayerSwap_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  alignedBlackDartLayerSwap homega heta hdegree (doubledAlignedBlackDart homega heta hdegree false x) = doubledAlignedBlackDart homega heta hdegree true x := by
-- proof
  apply ScratchLocalRetieC.alignedBlackDartLayerSwap_active homega heta hdegree x

/--
[alignedBlackDartLayerSwap_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedBlackDartLayerSwap_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) d)) :
-- imply
  alignedBlackDartLayerSwap homega heta hdegree d = d := by
-- proof
  apply ScratchLocalRetieC.alignedBlackDartLayerSwap_inactive homega heta hdegree d hinactive

/--
[alignedBlackDartLayerSwap_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedBlackDartLayerSwap_power_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
  {k : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hk : k < finiteFirstReturnTime (alignedBoundaryPerm homega heta hdegree false) (activeBlackDart (omega := omega) (eta := eta)) (doubledAlignedBlackDartEquiv homega heta hdegree false x)) :
-- imply
  alignedBlackDartLayerSwap homega heta hdegree ((alignedBoundaryPerm homega heta hdegree false ^ k) (doubledAlignedBlackDart homega heta hdegree false x)) = (alignedBoundaryPerm homega heta hdegree true ^ k) (doubledAlignedBlackDart homega heta hdegree true x) := by
-- proof
  apply ScratchLocalRetieC.alignedBlackDartLayerSwap_power homega heta hdegree x k hk

/--
[finiteFirstReturnSegment_aligned_eq_map_layerSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma finiteFirstReturnSegment_aligned_eq_map_layerSwap_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  finiteFirstReturnSegment (alignedBoundaryPerm homega heta hdegree true) (activeBlackDart (omega := omega) (eta := eta)) (doubledAlignedBlackDartEquiv homega heta hdegree true x) = (finiteFirstReturnSegment (alignedBoundaryPerm homega heta hdegree false) (activeBlackDart (omega := omega) (eta := eta)) (doubledAlignedBlackDartEquiv homega heta hdegree false x)).map (alignedBlackDartLayerSwap homega heta hdegree) := by
-- proof
  apply ScratchLocalRetieC.finiteFirstReturnSegment_aligned_eq_map_layerSwap homega heta hdegree x

/--
[doubledAlignedBoundarySegments_eq_map_layerSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma doubledAlignedBoundarySegments_eq_map_layerSwap_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {states : List (DoubledAlignedState omega eta)}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  doubledAlignedBoundarySegments homega heta hdegree true states = (doubledAlignedBoundarySegments homega heta hdegree false states).map (alignedBlackDartLayerSwap homega heta hdegree) := by
-- proof
  apply ScratchLocalRetieC.doubledAlignedBoundarySegments_eq_map_layerSwap homega heta hdegree states

/--
[doubledAlignedFirstReturnPerm_false_arrival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma doubledAlignedFirstReturnPerm_false_arrival_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  doubledAlignedBlackDartEquiv homega heta hdegree false (doubledAlignedFirstReturnPerm homega heta hdegree x) = finiteFirstReturn (alignedBoundaryPerm homega heta hdegree false) (activeBlackDart (omega := omega) (eta := eta)) (doubledAlignedBlackDartEquiv homega heta hdegree false x) := by
-- proof
  apply ScratchLocalRetieC.doubledAlignedFirstReturnPerm_false_arrival homega heta hdegree x

/--
[doubledAlignedFirstReturnPerm_true_common_arrival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma doubledAlignedFirstReturnPerm_true_common_arrival_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (finiteFirstReturn (alignedBoundaryPerm homega heta hdegree true) (activeBlackDart (omega := omega) (eta := eta)) (doubledAlignedBlackDartEquiv homega heta hdegree true x)).1 = (doubledAlignedBlackDartEquiv homega heta hdegree false (doubledAlignedFirstReturnPerm homega heta hdegree x)).1 := by
-- proof
  apply ScratchLocalRetieC.doubledAlignedFirstReturnPerm_true_common_arrival homega heta hdegree x

/--
[exists_aligned_chunk_split_of_flatten_eq_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma exists_aligned_chunk_split_of_flatten_eq_append_eq
  {chunks : List (List A)}
  {left right : List A}
-- given
  (hchunks : chunks ≠ [])
  (hnonempty : forall chunk, chunk ∈ chunks -> chunk ≠ [])
  (hsplit : chunks.flatten = left ++ right) :
-- imply
  exists before chunk after chunkLeft chunkRight, chunks = before ++ chunk :: after /\ chunk = chunkLeft ++ chunkRight /\ left = before.flatten ++ chunkLeft /\ right = chunkRight ++ after.flatten := by
-- proof
  apply ScratchLocalRetieC.exists_aligned_chunk_split_of_flatten_eq_append chunks hchunks hnonempty left right hsplit

/--
[flatten_alignedPermOrderedCycleFactorLists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma flatten_alignedPermOrderedCycleFactorLists_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D} :
-- imply
  (alignedPermOrderedCycleFactorLists sigma).flatten = permOrderedAllCycles sigma := by
-- proof
  apply ScratchLocalRetieC.flatten_alignedPermOrderedCycleFactorLists sigma

/--
[alignedPermOrderedCycleFactorLists_chunk_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedPermOrderedCycleFactorLists_chunk_ne_nil_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {chunk : List D}
-- given
  (hchunk : chunk ∈ alignedPermOrderedCycleFactorLists sigma) :
-- imply
  chunk ≠ [] := by
-- proof
  apply ScratchLocalRetieC.alignedPermOrderedCycleFactorLists_chunk_ne_nil sigma chunk hchunk

/--
[permOrderedCycleFactor_getElem_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma permOrderedCycleFactor_getElem_succ_eq
  [Fintype D]
  [DecidableEq D]
  {sigma cycle : Equiv.Perm D}
  {k : Nat}
-- given
  (hcycle : cycle ∈ sigma.cycleFactorsFinset)
  (hk : k + 1 < (permOrderedCycleFactor sigma cycle hcycle).length) :
-- imply
  sigma (permOrderedCycleFactor sigma cycle hcycle)[k] = (permOrderedCycleFactor sigma cycle hcycle)[k + 1] := by
-- proof
  apply ScratchLocalRetieC.permOrderedCycleFactor_getElem_succ sigma cycle hcycle k hk

/--
[permOrderedCycleFactor_getElem_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma permOrderedCycleFactor_getElem_last_eq
  [Fintype D]
  [DecidableEq D]
  {sigma cycle : Equiv.Perm D}
-- given
  (hcycle : cycle ∈ sigma.cycleFactorsFinset)
  (hnonempty : permOrderedCycleFactor sigma cycle hcycle ≠ []) :
-- imply
  sigma ((permOrderedCycleFactor sigma cycle hcycle).getLast hnonempty) = (permOrderedCycleFactor sigma cycle hcycle).head hnonempty := by
-- proof
  apply ScratchLocalRetieC.permOrderedCycleFactor_getElem_last sigma cycle hcycle hnonempty

/--
[flatten_alignedPermOrderedAllOrbitLists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma flatten_alignedPermOrderedAllOrbitLists_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D} :
-- imply
  (alignedPermOrderedAllOrbitLists sigma).flatten = alignedPermOrderedAllOrbits sigma := by
-- proof
  apply ScratchLocalRetieC.flatten_alignedPermOrderedAllOrbitLists sigma

/--
[alignedPermOrderedAllOrbitLists_chunk_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedPermOrderedAllOrbitLists_chunk_ne_nil_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {chunk : List D}
-- given
  (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma) :
-- imply
  chunk ≠ [] := by
-- proof
  apply ScratchLocalRetieC.alignedPermOrderedAllOrbitLists_chunk_ne_nil sigma chunk hchunk

/--
[alignedPermOrderedAllOrbitLists_getElem_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedPermOrderedAllOrbitLists_getElem_succ_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {chunk : List D}
  {k : Nat}
-- given
  (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
  (hk : k + 1 < chunk.length) :
-- imply
  sigma chunk[k] = chunk[k + 1] := by
-- proof
  apply ScratchLocalRetieC.alignedPermOrderedAllOrbitLists_getElem_succ sigma chunk hchunk k hk

/--
[alignedPermOrderedAllOrbitLists_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedPermOrderedAllOrbitLists_getLast_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {chunk : List D}
-- given
  (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
  (hnonempty : chunk ≠ []) :
-- imply
  sigma (chunk.getLast hnonempty) = chunk.head hnonempty := by
-- proof
  apply ScratchLocalRetieC.alignedPermOrderedAllOrbitLists_getLast sigma chunk hchunk hnonempty

/--
[alignedPermOrderedAllOrbitLists_mem_forward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedPermOrderedAllOrbitLists_mem_forward_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {chunk : List D}
  {x : D}
-- given
  (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
  (hx : x ∈ chunk) :
-- imply
  sigma x ∈ chunk := by
-- proof
  apply ScratchLocalRetieC.alignedPermOrderedAllOrbitLists_mem_forward sigma chunk hchunk x hx

/--
[alignedPermOrderedAllOrbitLists_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedPermOrderedAllOrbitLists_mem_iff_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {chunk : List D}
  {x : D}
-- given
  (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma) :
-- imply
  sigma x ∈ chunk ↔ x ∈ chunk := by
-- proof
  apply ScratchLocalRetieC.alignedPermOrderedAllOrbitLists_mem_iff sigma chunk hchunk x

/--
[alignedPermOrderedOrbitChunk_left_forward_of_ne_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedPermOrderedOrbitChunk_left_forward_of_ne_last_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {chunk left right : List D}
  {x : D}
-- given
  (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
  (hsplit : chunk = left ++ right)
  (hleft : left ≠ [])
  (hx : x ∈ left)
  (hne : x ≠ left.getLast hleft) :
-- imply
  sigma x ∈ left := by
-- proof
  apply ScratchLocalRetieC.alignedPermOrderedOrbitChunk_left_forward_of_ne_last sigma chunk left right hchunk hsplit hleft x hx hne

/--
[alignedPermOrderedOrbitChunk_right_forward_of_ne_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedPermOrderedOrbitChunk_right_forward_of_ne_last_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {chunk left right : List D}
  {x : D}
-- given
  (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
  (hsplit : chunk = left ++ right)
  (hright : right ≠ [])
  (hx : x ∈ right)
  (hne : x ≠ right.getLast hright) :
-- imply
  sigma x ∈ right := by
-- proof
  apply ScratchLocalRetieC.alignedPermOrderedOrbitChunk_right_forward_of_ne_last sigma chunk left right hchunk hsplit hright x hx hne

/--
[alignedPermOrderedOrbitChunk_split_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedPermOrderedOrbitChunk_split_boundary_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {chunk left right : List D}
-- given
  (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
  (hsplit : chunk = left ++ right)
  (hleft : left ≠ [])
  (hright : right ≠ []) :
-- imply
  sigma (left.getLast hleft) = right.head hright := by
-- proof
  apply ScratchLocalRetieC.alignedPermOrderedOrbitChunk_split_boundary sigma chunk left right hchunk hsplit hleft hright

/--
[alignedPermOrderedOrbitChunk_split_entry_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedPermOrderedOrbitChunk_split_entry_boundary_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {chunk left right : List D}
-- given
  (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
  (hsplit : chunk = left ++ right)
  (hleft : left ≠ [])
  (hright : right ≠ []) :
-- imply
  sigma (right.getLast hright) = left.head hleft := by
-- proof
  apply ScratchLocalRetieC.alignedPermOrderedOrbitChunk_split_entry_boundary sigma chunk left right hchunk hsplit hleft hright

/--
[exists_aligned_orbit_chunk_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma exists_aligned_orbit_chunk_cut_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {left right : List D}
-- given
  (hsplit : alignedPermOrderedAllOrbits sigma = left ++ right)
  (hne : alignedPermOrderedAllOrbits sigma ≠ []) :
-- imply
  exists before cut after cutLeft cutRight, alignedPermOrderedAllOrbitLists sigma = before ++ cut :: after /\ cut = cutLeft ++ cutRight /\ left = before.flatten ++ cutLeft /\ right = cutRight ++ after.flatten := by
-- proof
  apply ScratchLocalRetieC.exists_aligned_orbit_chunk_cut sigma left right hsplit hne

/--
[sum_map_permOrderedAllCycles_eq_support_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma sum_map_permOrderedAllCycles_eq_support_aligned_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
-- given
  (f : D -> Int) :
-- imply
  ((permOrderedAllCycles sigma).map f).sum = ∑ d ∈ sigma.support, f d := by
-- proof
  apply ScratchLocalRetieC.sum_map_permOrderedAllCycles_eq_support_aligned sigma f

/--
[sum_map_alignedPermOrderedAllOrbits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma sum_map_alignedPermOrderedAllOrbits_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
-- given
  (f : D -> Int) :
-- imply
  ((alignedPermOrderedAllOrbits sigma).map f).sum = ∑ d, f d := by
-- proof
  apply ScratchLocalRetieC.sum_map_alignedPermOrderedAllOrbits sigma f

/--
[mem_permOrderedCycleFactor_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma mem_permOrderedCycleFactor_iff_eq
  [Fintype D]
  [DecidableEq D]
  {sigma cycle : Equiv.Perm D}
  {d : D}
-- given
  (hcycle : cycle ∈ sigma.cycleFactorsFinset) :
-- imply
  d ∈ permOrderedCycleFactor sigma cycle hcycle ↔ d ∈ cycle.support := by
-- proof
  apply ScratchLocalRetieC.mem_permOrderedCycleFactor_iff sigma cycle hcycle d

/--
[mem_permOrderedAllCycles_iff_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma mem_permOrderedAllCycles_iff_support_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {d : D} :
-- imply
  d ∈ permOrderedAllCycles sigma ↔ d ∈ sigma.support := by
-- proof
  apply ScratchLocalRetieC.mem_permOrderedAllCycles_iff_support sigma d

/--
[mem_alignedPermOrderedAllOrbits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma mem_alignedPermOrderedAllOrbits_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {d : D} :
-- imply
  d ∈ alignedPermOrderedAllOrbits sigma := by
-- proof
  apply ScratchLocalRetieC.mem_alignedPermOrderedAllOrbits sigma d

/--
[length_alignedPermOrderedAllOrbits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma length_alignedPermOrderedAllOrbits_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D} :
-- imply
  (alignedPermOrderedAllOrbits sigma).length = Fintype.card D := by
-- proof
  apply ScratchLocalRetieC.length_alignedPermOrderedAllOrbits sigma

/--
[alignedPermOrderedAllOrbits_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedPermOrderedAllOrbits_nodup_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D} :
-- imply
  (alignedPermOrderedAllOrbits sigma).Nodup := by
-- proof
  apply ScratchLocalRetieC.alignedPermOrderedAllOrbits_nodup sigma

/--
[alignedPermOrderedAllOrbitLists_chunk_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedPermOrderedAllOrbitLists_chunk_nodup_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {chunk : List D}
-- given
  (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma) :
-- imply
  chunk.Nodup := by
-- proof
  apply ScratchLocalRetieC.alignedPermOrderedAllOrbitLists_chunk_nodup sigma chunk hchunk

/--
[alignedPermOrderedOrbitChunk_mem_left_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedPermOrderedOrbitChunk_mem_left_iff_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {chunk left right : List D}
  {x : D}
-- given
  (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
  (hsplit : chunk = left ++ right)
  (hleft : left ≠ [])
  (hright : right ≠ []) :
-- imply
  sigma x ∈ left ↔ (x ∈ left ∧ x ≠ left.getLast hleft) ∨ x = right.getLast hright := by
-- proof
  apply ScratchLocalRetieC.alignedPermOrderedOrbitChunk_mem_left_iff sigma chunk left right hchunk hsplit hleft hright x

/--
[alignedPermOrderedOrbitPrefix_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma alignedPermOrderedOrbitPrefix_mem_iff_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {before : List (List D)}
  {chunk : List D}
  {after : List (List D)}
  {left right : List D}
  {x : D}
-- given
  (hall : alignedPermOrderedAllOrbitLists sigma = before ++ chunk :: after)
  (hsplit : chunk = left ++ right)
  (hleft : left ≠ [])
  (hright : right ≠ []) :
-- imply
  sigma x ∈ before.flatten ++ left ↔ (x ∈ before.flatten ++ left ∧ x ≠ left.getLast hleft) ∨ x = right.getLast hright := by
-- proof
  apply ScratchLocalRetieC.alignedPermOrderedOrbitPrefix_mem_iff sigma before chunk after left right hall hsplit hleft hright x

/--
[exists_list_prefix_map_sum_eq_of_zeroOrUnitSteps_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma exists_list_prefix_map_sum_eq_of_zeroOrUnitSteps_aligned_eq
  {items : List A}
  {target total : Int}
-- given
  (step : A -> Int)
  (hsteps : forall x, x ∈ items -> step x = 0 \/ step x = 1 \/ step x = -1)
  (hsum : (items.map step).sum = total)
  (htarget_nonneg : 0 <= target)
  (htarget_le : target <= total) :
-- imply
  exists pre suf : List A, items = pre ++ suf /\ (pre.map step).sum = target := by
-- proof
  apply ScratchLocalRetieC.exists_list_prefix_map_sum_eq_of_zeroOrUnitSteps_aligned items step hsteps target total hsum htarget_nonneg htarget_le

/--
[exists_two_unit_blocks_of_alignedPermOrderedAllOrbits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma exists_two_unit_blocks_of_alignedPermOrderedAllOrbits_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
-- given
  (step : D -> Int)
  (hsteps : forall d, step d = 0 \/ step d = 1 \/ step d = -1)
  (hsum : ∑ d, step d = 2) :
-- imply
  exists first second : List D, alignedPermOrderedAllOrbits sigma = first ++ second /\ (first.map step).sum = 1 /\ (second.map step).sum = 1 := by
-- proof
  apply ScratchLocalRetieC.exists_two_unit_blocks_of_alignedPermOrderedAllOrbits sigma step hsteps hsum

/--
[doubledAlignedCharge_zeroOrUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma doubledAlignedCharge_zeroOrUnit_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  doubledAlignedCharge hdegree x = 0 \/ doubledAlignedCharge hdegree x = 1 \/ doubledAlignedCharge hdegree x = -1 := by
-- proof
  apply ScratchLocalRetieC.doubledAlignedCharge_zeroOrUnit hdegree x

/--
[sum_doubledAlignedCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma sum_doubledAlignedCharge_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (∑ d : SixVertexOrientedDisagreementDart omega eta, ∑ branch : Bool, doubledAlignedCharge hdegree (d, branch)) = ∑ d : SixVertexOrientedDisagreementDart omega eta, sixVertexDegreeTwoStrandStepSeamSign hdegree d := by
-- proof
  apply ScratchLocalRetieC.sum_doubledAlignedCharge hdegree

/--
[sum_doubledAlignedCharge_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma sum_doubledAlignedCharge_eq_two_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n) :
-- imply
  (∑ d : SixVertexOrientedDisagreementDart omega eta, ∑ branch : Bool, doubledAlignedCharge hdegree (d, branch)) = 2 := by
-- proof
  apply ScratchLocalRetieC.sum_doubledAlignedCharge_eq_two homega heta hdegree n homegaSector hetaSector hn

/--
[DoubledAlignedUnitOrbitSplit.first_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma first_nodup_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {split : DoubledAlignedUnitOrbitSplit homega heta hdegree}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  split.first.Nodup := by
-- proof
  apply ScratchLocalRetieC.DoubledAlignedUnitOrbitSplit.first_nodup homega heta hdegree split

/--
[exists_doubledAlignedUnitOrbitSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma exists_doubledAlignedUnitOrbitSplit_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n) :
-- imply
  Nonempty (DoubledAlignedUnitOrbitSplit homega heta hdegree) := by
-- proof
  apply ScratchLocalRetieC.exists_doubledAlignedUnitOrbitSplit homega heta hdegree n homegaSector hetaSector hn

/--
[canonicalDoubledAlignedSelectedStates_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma canonicalDoubledAlignedSelectedStates_nodup_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n) :
-- imply
  (canonicalDoubledAlignedSelectedStates homega heta hdegree n homegaSector hetaSector hn).Nodup := by
-- proof
  apply ScratchLocalRetieC.canonicalDoubledAlignedSelectedStates_nodup homega heta hdegree n homegaSector hetaSector hn

/--
[exists_canonicalDoubledAlignedOrbitChunkCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma exists_canonicalDoubledAlignedOrbitChunkCut_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n) :
-- imply
  let split := canonicalDoubledAlignedUnitOrbitSplit homega heta hdegree n homegaSector hetaSector hn exists before cut after cutLeft cutRight, alignedPermOrderedAllOrbitLists (doubledAlignedFirstReturnPerm homega heta hdegree) = before ++ cut :: after /\ cut = cutLeft ++ cutRight /\ split.first = before.flatten ++ cutLeft /\ split.second = cutRight ++ after.flatten := by
-- proof
  apply ScratchLocalRetieC.exists_canonicalDoubledAlignedOrbitChunkCut homega heta hdegree n homegaSector hetaSector hn

/--
[CanonicalDoubledAlignedOrbitChunkCut.cut_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma cut_mem_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
  {cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n homegaSector hetaSector hn}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n) :
-- imply
  cut.cut ∈ alignedPermOrderedAllOrbitLists (doubledAlignedFirstReturnPerm homega heta hdegree) := by
-- proof
  apply ScratchLocalRetieC.CanonicalDoubledAlignedOrbitChunkCut.cut_mem homega heta hdegree n homegaSector hetaSector hn cut

/--
[CanonicalDoubledAlignedOrbitChunkCut.proper_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma proper_boundary_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
  {cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n homegaSector hetaSector hn}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n)
  (hleft : cut.cutLeft ≠ [])
  (hright : cut.cutRight ≠ []) :
-- imply
  doubledAlignedFirstReturnPerm homega heta hdegree (cut.cutLeft.getLast hleft) = cut.cutRight.head hright := by
-- proof
  apply ScratchLocalRetieC.CanonicalDoubledAlignedOrbitChunkCut.proper_boundary homega heta hdegree n homegaSector hetaSector hn cut hleft hright

/--
[CanonicalDoubledAlignedOrbitChunkCut.proper_entry_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma proper_entry_boundary_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
  {cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n homegaSector hetaSector hn}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n)
  (hleft : cut.cutLeft ≠ [])
  (hright : cut.cutRight ≠ []) :
-- imply
  doubledAlignedFirstReturnPerm homega heta hdegree (cut.cutRight.getLast hright) = cut.cutLeft.head hleft := by
-- proof
  apply ScratchLocalRetieC.CanonicalDoubledAlignedOrbitChunkCut.proper_entry_boundary homega heta hdegree n homegaSector hetaSector hn cut hleft hright

/--
[CanonicalDoubledAlignedOrbitChunkCut.transition_states_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma transition_states_ne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
  {cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n homegaSector hetaSector hn}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n)
  (hleft : cut.cutLeft ≠ [])
  (hright : cut.cutRight ≠ []) :
-- imply
  cut.cutRight.head hright ≠ cut.cutLeft.head hleft := by
-- proof
  apply ScratchLocalRetieC.CanonicalDoubledAlignedOrbitChunkCut.transition_states_ne homega heta hdegree n homegaSector hetaSector hn cut hleft hright

/--
[CanonicalDoubledAlignedOrbitChunkCut.selected_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma selected_mem_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
  {cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n homegaSector hetaSector hn}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n)
  (hleft : cut.cutLeft ≠ [])
  (hright : cut.cutRight ≠ []) :
-- imply
  doubledAlignedFirstReturnPerm homega heta hdegree x ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n homegaSector hetaSector hn ↔ (x ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n homegaSector hetaSector hn ∧ x ≠ cut.cutLeft.getLast hleft) ∨ x = cut.cutRight.getLast hright := by
-- proof
  apply ScratchLocalRetieC.CanonicalDoubledAlignedOrbitChunkCut.selected_mem_iff homega heta hdegree n homegaSector hetaSector hn cut hleft hright x

/--
[CanonicalDoubledAlignedOrbitChunkCut.not_selected_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma not_selected_invariant_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
  {cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n homegaSector hetaSector hn}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n)
  (hleft : cut.cutLeft ≠ [])
  (hright : cut.cutRight ≠ []) :
-- imply
  ¬ forall x : DoubledAlignedState omega eta, (doubledAlignedFirstReturnPerm homega heta hdegree x ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n homegaSector hetaSector hn ↔ x ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n homegaSector hetaSector hn) := by
-- proof
  apply ScratchLocalRetieC.CanonicalDoubledAlignedOrbitChunkCut.not_selected_invariant homega heta hdegree n homegaSector hetaSector hn cut hleft hright

/--
[canonicalDoubledAlignedOrbitChunkCut_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma canonicalDoubledAlignedOrbitChunkCut_cases_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n) :
-- imply
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree n homegaSector hetaSector hn cut.cutLeft = [] ∨ cut.cutRight = [] ∨ (cut.cutLeft ≠ [] ∧ cut.cutRight ≠ []) := by
-- proof
  apply ScratchLocalRetieC.canonicalDoubledAlignedOrbitChunkCut_cases homega heta hdegree n homegaSector hetaSector hn

/--
[omega_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma omega_ice_eq :
-- imply
  omega.IceRule := by
-- proof
  apply ScratchLocalRetieC.FourByTwoBondAudit.omega_ice

/--
[eta_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma eta_ice_eq :
-- imply
  eta.IceRule := by
-- proof
  apply ScratchLocalRetieC.FourByTwoBondAudit.eta_ice

/--
[locallyDegreeTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma locallyDegreeTwo_eq :
-- imply
  SixVertexLocallyDegreeTwo omega eta := by
-- proof
  apply ScratchLocalRetieC.FourByTwoBondAudit.locallyDegreeTwo

/--
[cutVertex_alignedRetie_premises](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma cutVertex_alignedRetie_premises_eq :
-- imply
  let p := sixVertexLocalIncomingPattern omega cutVertex let q := sixVertexLocalIncomingPattern eta cutVertex p.Ice /\ q.Ice /\ (sixVertexLocalDisagreementSides p q).card = 2 /\ compatible true p /\ compatible true q /\ p (0 : Fin 4) != q (0 : Fin 4) /\ p (localMate true (localMate true (0 : Fin 4))) != q (localMate true (localMate true (0 : Fin 4))) := by
-- proof
  apply ScratchLocalRetieC.FourByTwoBondAudit.cutVertex_alignedRetie_premises

/--
[singletonPrefix_west_bond_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma singletonPrefix_west_bond_failure_eq :
-- imply
  singletonPrefixPattern false cutVertex 0 = singletonPrefixPattern false (SixVertexArrows.cyclicPred sixVertexFourByTwoTorus.width_pos cutVertex.1, cutVertex.2) 1 := by
-- proof
  apply ScratchLocalRetieC.FourByTwoBondAudit.singletonPrefix_west_bond_failure

/--
[singletonPrefix_not_bondConsistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean)
-/
@[path]
private lemma singletonPrefix_not_bondConsistent_eq :
-- imply
  Not ((forall (layer : Bool) (v : sixVertexFourByTwoTorus.Vertex), singletonPrefixPattern layer v 0 = !singletonPrefixPattern layer (SixVertexArrows.cyclicPred sixVertexFourByTwoTorus.width_pos v.1, v.2) 1) /\ (forall (layer : Bool) (v : sixVertexFourByTwoTorus.Vertex), singletonPrefixPattern layer v 2 = !singletonPrefixPattern layer (v.1, SixVertexArrows.cyclicPred sixVertexFourByTwoTorus.height_pos v.2) 3)) := by
-- proof
  apply ScratchLocalRetieC.FourByTwoBondAudit.singletonPrefix_not_bondConsistent


-- created on 2026-10-23
