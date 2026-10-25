/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part21
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagDecoratedSourceRowMask_injOn_crossTraceFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Set.InjOn (fun z : LPReplicaOffdiagDecoratedSource G sites i j q =>
      lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z))
      (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
        G sites i j q u) := by
  classical
  intro z hz w hw hmask
  simp only [Finset.mem_coe] at hz hw
  apply lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q
  let sz := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z
  let sw := lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w
  have htracez : lpReplicaOrbitFourColorSlotCrossNormalize G sites q sz = u := by
    simpa only [lpReplicaOffdiagDecoratedSourceCrossTraceFiber,
      Finset.mem_filter, Finset.mem_univ, true_and,
      lpReplicaOffdiagDecoratedSourceCrossTrace] using hz
  have htracew : lpReplicaOrbitFourColorSlotCrossNormalize G sites q sw = u := by
    simpa only [lpReplicaOffdiagDecoratedSourceCrossTraceFiber,
      Finset.mem_filter, Finset.mem_univ, true_and,
      lpReplicaOffdiagDecoratedSourceCrossTrace] using hw
  change lpReplicaOrbitFourColorSlotRowMask G sites q sz =
    lpReplicaOrbitFourColorSlotRowMask G sites q sw at hmask
  calc
    sz = lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitFourColorSlotRowMask G sites q sz)
        (lpReplicaOrbitFourColorSlotCrossNormalize G sites q sz) :=
      (lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize
        G sites q sz).symm
    _ = lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitFourColorSlotRowMask G sites q sw)
        (lpReplicaOrbitFourColorSlotCrossNormalize G sites q sw) := by
      rw [hmask, htracez, htracew]
    _ = sw := lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize
      G sites q sw


theorem lpReplicaOffdiagDecoratedTargetBranchedRowMask_injOn_crossTraceFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Set.InjOn (fun y : LPReplicaOffdiagDecoratedTarget G sites i j q =>
      ((lpReplicaOffdiagDecoratedTargetBranchedSlotState
          G sites i j q y).1,
        lpReplicaOrbitFourColorSlotRowMask G sites q
          (lpReplicaOffdiagDecoratedTargetBranchedSlotState
            G sites i j q y).2))
      (lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u) := by
  classical
  intro y hy w hw hmask
  simp only [Finset.mem_coe] at hy hw
  have hbranch := congrArg (fun p : Bool ×
      Finset (LPReplicaOrbitCommonSlot G sites q) => p.1) hmask
  let sy := (lpReplicaOffdiagDecoratedTargetBranchedSlotState
    G sites i j q y).2
  let sw := (lpReplicaOffdiagDecoratedTargetBranchedSlotState
    G sites i j q w).2
  have htracey : lpReplicaOrbitFourColorSlotCrossNormalize G sites q sy = u := by
    have h := (Finset.mem_filter.mp hy).2
    exact h
  have htracew : lpReplicaOrbitFourColorSlotCrossNormalize G sites q sw = u := by
    have h := (Finset.mem_filter.mp hw).2
    exact h
  have hrow := congrArg (fun p : Bool ×
      Finset (LPReplicaOrbitCommonSlot G sites q) => p.2) hmask
  change lpReplicaOrbitFourColorSlotRowMask G sites q sy =
    lpReplicaOrbitFourColorSlotRowMask G sites q sw at hrow
  have hstate : sy = sw := by
    calc
      sy = lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitFourColorSlotRowMask G sites q sy)
          (lpReplicaOrbitFourColorSlotCrossNormalize G sites q sy) :=
        (lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize
          G sites q sy).symm
      _ = lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitFourColorSlotRowMask G sites q sw)
          (lpReplicaOrbitFourColorSlotCrossNormalize G sites q sw) := by
        rw [hrow, htracey, htracew]
      _ = sw := lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize
        G sites q sw
  apply lpReplicaOffdiagDecoratedTargetBranchedSlotState_injective
    G sites i j q
  exact Prod.ext hbranch hstate


theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiber_card_eq_masks
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber G sites i j q u).card =
      (lpReplicaOffdiagDecoratedSourceCrossTraceMasks
        G sites i j q u).card := by
  classical
  symm
  exact Finset.card_image_iff.mpr
    (lpReplicaOffdiagDecoratedSourceRowMask_injOn_crossTraceFiber
      G sites i j q u)


theorem lpReplicaOffdiagBalancedOutputCrossTraceFiber_card_eq_branchedMasks
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q u).card =
      (lpReplicaOffdiagBalancedOutputCrossTraceBranchedMasks
        G sites i j q u).card := by
  classical
  symm
  exact Finset.card_image_iff.mpr
    (lpReplicaOffdiagDecoratedTargetBranchedRowMask_injOn_crossTraceFiber
      G sites i j q u)


theorem lpReplica_half_ne_doubledBoundary_of_nonempty
    (X D : Finset (LPReplicaCurrentVertex V))
    (hD : D = X ∆ X.map lpReplicaCurrentReflect.toEmbedding)
    (hDne : D.Nonempty) : X ≠ D := by
  intro hXD
  have hself : X = X ∆ X.map lpReplicaCurrentReflect.toEmbedding :=
    hXD.trans hD
  have hreflectEmpty :
      X.map lpReplicaCurrentReflect.toEmbedding = ∅ := by
    have hcancel : (∅ : Finset (LPReplicaCurrentVertex V)) =
        X.map lpReplicaCurrentReflect.toEmbedding := by
      calc
        ∅ = X ∆ X := by simp
        _ = X ∆ (X ∆ X.map lpReplicaCurrentReflect.toEmbedding) :=
          congrArg (fun Y => X ∆ Y) hself
        _ = X.map lpReplicaCurrentReflect.toEmbedding :=
          symmDiff_symmDiff_cancel_left _ _
    exact hcancel.symm
  have hXempty : X = ∅ := Finset.map_eq_empty.mp hreflectEmpty
  have hDempty : D = ∅ := by
    rw [hD, hXempty]
    simp
  exact Finset.nonempty_iff_ne_empty.mp hDne hDempty


theorem lpReplicaDecoratedSourceCanonicalHalfBranch_not_directTarget
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let Si := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
    let Sj := lpMatchingSeamSource
      (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
    let T := lpMatchingGhostSource
      (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
      lpReplicaCurrentGhost1
    match lpReplicaDecoratedSourceCanonicalHalfBranch
        G sites hsite hij q z with
    | Sum.inl b => b.1 ≠ Sj ∆ T
    | Sum.inr b => b.1 ≠ Si ∆ T := by
  dsimp only
  let branch := lpReplicaDecoratedSourceCanonicalHalfBranch
    G sites hsite hij q z
  change match branch with
    | Sum.inl b => b.1 ≠
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1
    | Sum.inr b => b.1 ≠
        lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1
  rcases hbranch : branch with left | right
  · change left.1 ≠
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1
    apply lpReplica_half_ne_doubledBoundary_of_nonempty
      left.1
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      left.2.2
    refine ⟨(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V), ?_⟩
    simp [lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff]
  · change right.1 ≠
      lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1
    apply lpReplica_half_ne_doubledBoundary_of_nonempty
      right.1
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1)
      right.2.2
    refine ⟨(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V), ?_⟩
    simp [lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff]


end
end StatMech.Ising
