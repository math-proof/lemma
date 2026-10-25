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
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part10
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagCoupledPairedCut_leftTarget
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) ∅ tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaCoupledPairedCut G sites m
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) tag)
    (hD : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
    (hA : (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) ∆
        (cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding) =
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) :
    ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCommonSlotsOfCopies
              G sites q m hm L cut.selector)
            (lpReplicaOrbitFourColorSlotStateOfTag
              G sites q m hm L tag) := by
  let y : LPReplicaOffdiagDecoratedTarget G sites i j q :=
    Sum.inl (lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast G sites m q
      _ _ _ tag hm hgate L cut hA hD)
  refine ⟨y, ?_, ?_⟩
  · dsimp only [LPReplicaOffdiagCoupledPairedOutput]
    left
    exact ⟨m, tag, hm, hgate, L, cut, hD, hA, rfl⟩
  · change lpReplicaOrientedFourColorSlotState G sites _ _ q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites _ _ q
          (lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast G sites m q
            _ _ _ tag hm hgate L cut hA hD)) = _
    exact lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast_slotState
      G sites m q _ _ _ tag hm hgate L cut hA hD


theorem lpReplicaOffdiagCoupledPairedCut_rightTarget
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) ∅ tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaCoupledPairedCut G sites m
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) tag)
    (hD : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
    (hA : (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) ∆
        (cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding) =
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j) :
    ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCommonSlotsOfCopies
              G sites q m hm L cut.selector)
            (lpReplicaOrbitFourColorSlotStateOfTag
              G sites q m hm L tag) := by
  let y : LPReplicaOffdiagDecoratedTarget G sites i j q :=
    Sum.inr (lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast G sites m q
      _ _ _ tag hm hgate L cut hA hD)
  refine ⟨y, ?_, ?_⟩
  · dsimp only [LPReplicaOffdiagCoupledPairedOutput]
    right
    exact ⟨m, tag, hm, hgate, L, cut, hD, hA, rfl⟩
  · change lpReplicaOrientedFourColorSlotState G sites _ _ q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites _ _ q
          (lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast G sites m q
            _ _ _ tag hm hgate L cut hA hD)) = _
    exact lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast_slotState
      G sites m q _ _ _ tag hm hgate L cut hA hD


theorem lpReplicaOffdiagCanonicalLastTwoPairedCutRealizable_target
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hrealize : LPReplicaOffdiagCanonicalLastTwoPairedCutRealizable
      G sites i j q hcard z) :
    ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧
        (lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).2 =
          lpReplicaOrbitFourColorSlotCrossToggle G sites q
            (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard)
            (lpReplicaOffdiagDecoratedSourceSlotState
              G sites i j q z) := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  change ∃ (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
      (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
      (hm : lpReplicaSymmetrizedProfile G sites m = q)
      (hgate : LPReplicaRowGate G sites m B ∅ tag)
      (L : LPReplicaProfileOrbitLabel G sites q m)
      (cut : LPReplicaCoupledPairedCut G sites m B tag),
    lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag =
        lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z ∧
      lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L cut.selector =
        lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard ∧
      (let D := cut.half ∆
        cut.half.map lpReplicaCurrentReflect.toEmbedding
       D = Sj ∆ T ∨ D = Si ∆ T) at hrealize
  obtain ⟨m, tag, hm, hgate, L, cut, hsource, hmask, hboundary⟩ := hrealize
  let D := cut.half ∆
    cut.half.map lpReplicaCurrentReflect.toEmbedding
  change D = Sj ∆ T ∨ D = Si ∆ T at hboundary
  rcases hboundary with hD | hD
  · have hA : B ∆ D = Si := by
      rw [hD]
      simp [B, symmDiff_assoc, symmDiff_comm, symmDiff_left_comm]
    obtain ⟨y, hy, hstate⟩ := lpReplicaOffdiagCoupledPairedCut_leftTarget
      G sites i j q m tag hm hgate L cut hD hA
    refine ⟨y, hy, ?_⟩
    rw [hstate, hmask, hsource]
  · have hA : B ∆ D = Sj := by
      rw [hD]
      simp [B, symmDiff_assoc, symmDiff_comm, symmDiff_left_comm]
    obtain ⟨y, hy, hstate⟩ := lpReplicaOffdiagCoupledPairedCut_rightTarget
      G sites i j q m tag hm hgate L cut hD hA
    refine ⟨y, hy, ?_⟩
    rw [hstate, hmask, hsource]

set_option maxHeartbeats 800000 in


theorem lpReplicaOffdiagRightCoupledPairedCut_leftTarget
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (hgate : LPReplicaRowGate G sites m ∅ B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag)
    (hA : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding =
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
    (hD : B ∆ (cut.half ∆
        cut.half.map lpReplicaCurrentReflect.toEmbedding) =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) :
    ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q y).2 =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitCommonSlotsOfCopies
            G sites q m hm L cut.selector)
          (lpReplicaOrbitFourColorSlotStateOfTag
            G sites q m hm L tag) := by
  refine ⟨Sum.inl
    (lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast
      G sites m q B
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
        tag hm hB hgate L cut hA hD), ?_⟩
  exact lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast_slotState
    G sites m q B
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      tag hm hB hgate L cut hA hD

set_option maxHeartbeats 800000 in


theorem lpReplicaOffdiagRightCoupledPairedCut_rightTarget
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (B : Finset (LPReplicaCurrentVertex V))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
    (hgate : LPReplicaRowGate G sites m ∅ B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (cut : LPReplicaRightCoupledPairedCut G sites m B tag)
    (hA : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding =
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
    (hD : B ∆ (cut.half ∆
        cut.half.map lpReplicaCurrentReflect.toEmbedding) =
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) :
    ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q y).2 =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitCommonSlotsOfCopies
            G sites q m hm L cut.selector)
          (lpReplicaOrbitFourColorSlotStateOfTag
            G sites q m hm L tag) := by
  refine ⟨Sum.inr
    (lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast
      G sites m q B
        (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1)
        tag hm hB hgate L cut hA hD), ?_⟩
  exact lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast_slotState
    G sites m q B
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      tag hm hB hgate L cut hA hD

set_option maxHeartbeats 4000000 in


theorem lpReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable_target
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hrealize : LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable
      G sites i j q hcard z) :
    ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q,
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q y).2 =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard)
          (lpReplicaOffdiagDecoratedSourceSlotState
            G sites i j q z) := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  let B := Si ∆ Sj ∆ T
  let hfixed : B.map lpReplicaCurrentReflect.toEmbedding = B := by
    simpa only [B] using
      lpReplicaCurrentReflect_offdiagSource G sites i j
  let d := lpReplicaDecoratedOrbitAtomFixedRowGateData
    G sites ∅ B q hfixed z
  change ∃ cut : LPReplicaRightCoupledPairedCut
      G sites z.1.1.1 B d.1,
    lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
        z.1.1.2 z.2.2 cut.selector =
      lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard ∧
    (let D := cut.half ∆
      cut.half.map lpReplicaCurrentReflect.toEmbedding
     D = Si ∨ D = Sj) at hrealize
  obtain ⟨cut, hmask, hboundary⟩ := hrealize
  have hsource :=
    lpReplicaOffdiagDecoratedSourceSlotState_fixedRowGateData
      G sites i j q z
  let D := cut.half ∆
    cut.half.map lpReplicaCurrentReflect.toEmbedding
  change D = Si ∨ D = Sj at hboundary
  rcases hboundary with hD | hD
  · have htarget : B ∆ D = Sj ∆ T := by
      rw [hD]
      simp [B, symmDiff_assoc, symmDiff_comm, symmDiff_left_comm]
    obtain ⟨y, hstate⟩ := lpReplicaOffdiagRightCoupledPairedCut_leftTarget
      G sites i j q z.1.1.1 B d.1 z.1.1.2 hfixed d.2 z.2.2
        cut hD htarget
    refine ⟨y, ?_⟩
    rw [hstate, hmask, ← hsource]
  · have htarget : B ∆ D = Si ∆ T := by
      rw [hD]
      simp [B, symmDiff_assoc, symmDiff_comm, symmDiff_left_comm]
    obtain ⟨y, hstate⟩ := lpReplicaOffdiagRightCoupledPairedCut_rightTarget
      G sites i j q z.1.1.1 B d.1 z.1.1.2 hfixed d.2 z.2.2
        cut hD htarget
    refine ⟨y, ?_⟩
    rw [hstate, hmask, ← hsource]


end
end StatMech.Ising
