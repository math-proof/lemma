/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutHallExact
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagProjection
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 800000 in


theorem lpReplicaPartialReflectTransportTag_cast_eq_coupledRaw
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (d : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m P))) :
    lpReplicaPartialReflectTransportTag G sites m P tag
        (cast (congrArg (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites))
            (lpReplicaCollisionProfile_compl_eq_partialReflectProfile
              G sites m P)) d) =
      lpReplicaCoupledReflectToggleTagRaw G sites m P tag d := by
  unfold lpReplicaPartialReflectTransportTag
    lpReplicaCoupledReflectToggleTagRaw lpReplicaPartialReflectTagRaw
    lpReplicaPartialReflectCopyEquiv
  apply congrArg (lpReplicaToggleRows G sites m P tag)
  apply congrArg (lpReplicaPartialReflectCopyEquivRaw G sites m P).symm
  exact (Equiv.cast (congrArg (StatMech.Sharpness.FluxEdgeCopy.Copy
    (lpReplicaCurrentGraph G sites))
      (lpReplicaCollisionProfile_compl_eq_partialReflectProfile
        G sites m P))).symm_apply_apply d


theorem lpReplicaOrbitFourColorSlotState_partialReflect_of_compatible
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hcompat : LPReplicaPartialReflectCommonSlotCompatible
      G sites q m hm L P) :
    lpReplicaOrbitFourColorSlotStateOfTag G sites q
        (lpReplicaPartialReflectProfile G sites m
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m P))
        ((lpReplicaSymmetrizedProfile_partialReflectCopies
          G sites m P).trans hm)
        (lpReplicaProfileOrbitLabelPartialReflectCopies
          G sites q m hm P L)
        (lpReplicaPartialReflectTransportTag G sites m P tag) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
        (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) := by
  apply LPReplicaOrbitFourColorSlotState.ext
  · rw [lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_allocation]
    rfl
  · rw [lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_color]
    funext x
    let Es := lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
    let Et := lpReplicaProfileCopyEquivCommonSlot G sites q
      (lpReplicaPartialReflectProfile G sites m
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m P))
      ((lpReplicaSymmetrizedProfile_partialReflectCopies
        G sites m P).trans hm)
      (lpReplicaProfileOrbitLabelPartialReflectCopies
        G sites q m hm P L)
    let E := lpReplicaPartialReflectCopyEquiv G sites m P
    let c := Es.symm x.1
    have hEt : Et (E c) = x.1 := by
      rw [hcompat c]
      exact Es.apply_symm_apply x.1
    have hinv : Et.symm x.1 = E c := by
      apply Et.injective
      rw [Et.apply_symm_apply, hEt]
    change lpReplicaRowTagEquivFin4
        (lpReplicaPartialReflectTransportTag G sites m P tag
          (Et.symm x.1)) =
      lpReplicaRowTagEquivFin4
        (lpReplicaToggleRows G sites m P tag (Es.symm x.1))
    rw [hinv]
    simp only [lpReplicaPartialReflectTransportTag, E, c, Es,
      Equiv.symm_apply_apply]


theorem lpReplicaOrientedFourColorSlotState_cast_targetBoundary
    (G : SimpleGraph V) (sites : I -> V)
    (A D E : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (h : D = E) (x : LPReplicaDecoratedOrbitAtom G sites A D q) :
    lpReplicaOrientedFourColorSlotState G sites A E q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A E q
          (cast (congrArg
            (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) h) x)) =
      lpReplicaOrientedFourColorSlotState G sites A D q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor
          G sites A D q x) := by
  subst E
  rfl


theorem lpReplicaOrientedFourColorSlotState_cast_sourceBoundary
    (G : SimpleGraph V) (sites : I -> V)
    (A C D : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (h : A = C) (x : LPReplicaDecoratedOrbitAtom G sites A D q) :
    lpReplicaOrientedFourColorSlotState G sites C D q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites C D q
          (cast (congrArg
            (fun Z => LPReplicaDecoratedOrbitAtom G sites Z D q) h) x)) =
      lpReplicaOrientedFourColorSlotState G sites A D q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor
          G sites A D q x) := by
  subst C
  rfl

set_option maxHeartbeats 800000 in


theorem lpReplicaDecoratedOrbitAtomOfCoupledPairedCut_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaCoupledPairedCut G sites m B tag) :
    let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
    lpReplicaOrientedFourColorSlotState G sites (B ∆ D) D q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites
          (B ∆ D) D q
          (lpReplicaDecoratedOrbitAtomOfCoupledPairedCut
            G sites m q B tag horbit hgate L cut)) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies
          G sites q m horbit L cut.selector)
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m horbit L tag) := by
  dsimp only
  unfold lpReplicaDecoratedOrbitAtomOfCoupledPairedCut
  dsimp only [id]
  rw [lpReplicaOrientedFourColorSlotState_cast_targetBoundary]
  rw [lpReplicaOrientedFourColorSlotState_ofRowGate]
  · exact lpReplicaOrbitFourColorSlotState_canonicalPartialReflect
      G sites q m horbit L cut.selector tag
  · exact lpReplica_half_symmDiff_reflect_fixed cut.half

set_option maxHeartbeats 800000 in


theorem lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (hgate : LPReplicaRowGate G sites m ∅ B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag) :
    let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
    lpReplicaOrientedFourColorSlotState G sites D (B ∆ D) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites
          D (B ∆ D) q
          (lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut
            G sites m q B tag horbit hB hgate L cut)) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies
          G sites q m horbit L cut.selector)
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m horbit L tag) := by
  dsimp only
  unfold lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut
  dsimp only [id]
  rw [lpReplicaOrientedFourColorSlotState_cast_targetBoundary]
  rw [lpReplicaOrientedFourColorSlotState_ofRowGate]
  · exact lpReplicaOrbitFourColorSlotState_canonicalPartialReflect
      G sites q m horbit L cut.selector tag
  · rw [lpReplica_map_symmDiff, hB,
      lpReplica_half_symmDiff_reflect_fixed]


theorem lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B A Dtarget : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m B ∅ tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaCoupledPairedCut G sites m B tag)
    (hA : B ∆ (cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding) = A)
    (hD : cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding = Dtarget) :
    lpReplicaOrientedFourColorSlotState G sites A Dtarget q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites
          A Dtarget q
          (lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast
            G sites m q B A Dtarget tag horbit hgate L cut hA hD)) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies
          G sites q m horbit L cut.selector)
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m horbit L tag) := by
  unfold lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast
  dsimp only [id]
  rw [lpReplicaOrientedFourColorSlotState_cast_targetBoundary]
  rw [lpReplicaOrientedFourColorSlotState_cast_sourceBoundary]
  exact lpReplicaDecoratedOrbitAtomOfCoupledPairedCut_slotState
    G sites m q B tag horbit hgate L cut
  all_goals assumption


theorem lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast_slotState
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B A Dtarget : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (horbit : lpReplicaSymmetrizedProfile G sites m = q)
    (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (hgate : LPReplicaRowGate G sites m ∅ B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag)
    (hA : cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding = A)
    (hD : B ∆ (cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding) = Dtarget) :
    lpReplicaOrientedFourColorSlotState G sites A Dtarget q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites
          A Dtarget q
          (lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast
            G sites m q B A Dtarget tag horbit hB hgate L cut hA hD)) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies
          G sites q m horbit L cut.selector)
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m horbit L tag) := by
  unfold lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast
  dsimp only [id]
  rw [lpReplicaOrientedFourColorSlotState_cast_targetBoundary]
  rw [lpReplicaOrientedFourColorSlotState_cast_sourceBoundary]
  exact lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut_slotState
    G sites m q B tag horbit hB hgate L cut
  all_goals assumption


theorem lpReplica_even_card_half_symmDiff_reflect_inter_leftSide
    (X : Finset (LPReplicaCurrentVertex V)) (hX : Even X.card) :
    Even ((X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∩
      lpReplicaCurrentLeftSide).card := by
  classical
  let L := lpReplicaCurrentLeftSide (V := V)
  let XL := X ∩ L
  let XR := X \ L
  let YR := XR.map lpReplicaCurrentReflect.toEmbedding
  have hsymm (x : LPReplicaCurrentVertex V) :
      lpReplicaCurrentReflect.symm x = lpReplicaCurrentReflect x := by
    apply lpReplicaCurrentReflect.injective
    rw [Equiv.apply_symm_apply, lpReplicaCurrentReflect_involutive]
  have hdecomp : (X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∩ L =
      XL ∆ YR := by
    ext x
    rcases x with (x | b)
    · rcases x with x | x <;>
        simp [L, XL, XR, YR, Finset.mem_symmDiff,
          lpReplicaCurrentLeftSide, lpReplicaCurrentLeftEmbedding,
          lpReplicaCurrentGhost0, hsymm]
    · cases b <;>
        simp [L, XL, XR, YR, Finset.mem_symmDiff,
          lpReplicaCurrentLeftSide, lpReplicaCurrentLeftEmbedding,
          lpReplicaCurrentGhost0, hsymm]
  have hYR : YR.card = XR.card := by
    dsimp only [YR]
    rw [Finset.card_map]
  have hsum : Even (XL.card + YR.card) := by
    rw [hYR]
    have hpartition := Finset.card_sdiff_add_card_inter X L
    dsimp only [XL, XR]
    rw [add_comm]
    rwa [hpartition]
  have hdisj : Disjoint (XL \ YR) (YR \ XL) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hx).1
  have hcard : (XL ∆ YR).card =
      (XL \ YR).card + (YR \ XL).card := by
    rw [show XL ∆ YR = (XL \ YR) ∪ (YR \ XL) by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]]
    exact Finset.card_union_of_disjoint hdisj
  rcases hsum with ⟨k, hk⟩
  have hXL := Finset.card_sdiff_add_card_inter XL YR
  have hYR' := Finset.card_sdiff_add_card_inter YR XL
  rw [Finset.inter_comm YR XL] at hYR'
  rw [hdecomp, hcard]
  refine ⟨k - (XL ∩ YR).card, ?_⟩
  omega


end
end StatMech.Ising
