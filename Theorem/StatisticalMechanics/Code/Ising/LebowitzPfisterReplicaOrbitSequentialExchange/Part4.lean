/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 800000 in


theorem lpReplicaOrbitFourColorSlotState_canonicalPartialReflect
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaOrbitFourColorSlotStateOfTag G sites q
        (lpReplicaPartialReflectProfile G sites m
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        ((lpReplicaSymmetrizedProfile_partialReflectCopies
          G sites m P).trans hm)
        (lpReplicaProfileOrbitLabelPartialReflectCopies
          G sites q m hm P L)
        (lpReplicaCanonicalPartialReflectToggleTag
          G sites q m hm L P tag) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m hm L tag) := by
  apply LPReplicaOrbitFourColorSlotState.ext
  · rw [lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_allocation]
    rfl
  · rw [lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_color]
    funext x
    let Es := lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
    let Et := lpReplicaProfileCopyEquivCommonSlot G sites q
      (lpReplicaPartialReflectProfile G sites m
        (profileFlux (lpReplicaCurrentGraph G sites) m P))
      ((lpReplicaSymmetrizedProfile_partialReflectCopies
        G sites m P).trans hm)
      (lpReplicaProfileOrbitLabelPartialReflectCopies
        G sites q m hm P L)
    change lpReplicaRowTagEquivFin4
        (lpReplicaCanonicalPartialReflectToggleTag
          G sites q m hm L P tag (Et.symm x.1)) =
      lpReplicaRowTagEquivFin4
        (lpReplicaToggleRows G sites m P tag (Es.symm x.1))
    apply congrArg lpReplicaRowTagEquivFin4
    apply congrArg (lpReplicaToggleRows G sites m P tag)
    let E := lpReplicaPartialReflectCanonicalCopyEquiv
      G sites q m hm L P
    apply E.injective
    rw [E.apply_symm_apply]
    unfold E lpReplicaPartialReflectCanonicalCopyEquiv
    change Et.symm x.1 = Et.symm (Es (Es.symm x.1))
    rw [Es.apply_symm_apply]

set_option maxHeartbeats 800000 in


theorem lpReplicaPartialReflectCanonicalCopyEquiv_edge
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : Copy (lpReplicaCurrentGraph G sites) m) :
    (lpReplicaPartialReflectCanonicalCopyEquiv
      G sites q m hm L P c).1 =
      if c ∈ P then lpReplicaCurrentEdgeReflect G sites c.1 else c.1 := by
  classical
  let Es := lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
  let Et := lpReplicaProfileCopyEquivCommonSlot G sites q
    (lpReplicaPartialReflectProfile G sites m
      (profileFlux (lpReplicaCurrentGraph G sites) m P))
    ((lpReplicaSymmetrizedProfile_partialReflectCopies
      G sites m P).trans hm)
    (lpReplicaProfileOrbitLabelPartialReflectCopies
      G sites q m hm P L)
  let E := lpReplicaPartialReflectCanonicalCopyEquiv
    G sites q m hm L P
  let sourceTag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag :=
    fun _ => (false, false)
  let sourceState := lpReplicaOrbitFourColorSlotStateOfTag
    G sites q m hm L sourceTag
  let targetState := lpReplicaOrbitFourColorSlotStateOfTag G sites q
    (lpReplicaPartialReflectProfile G sites m
      (profileFlux (lpReplicaCurrentGraph G sites) m P))
    ((lpReplicaSymmetrizedProfile_partialReflectCopies
      G sites m P).trans hm)
    (lpReplicaProfileOrbitLabelPartialReflectCopies
      G sites q m hm P L)
    (lpReplicaCanonicalPartialReflectToggleTag
      G sites q m hm L P sourceTag)
  have hstate : targetState =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
        sourceState :=
    lpReplicaOrbitFourColorSlotState_canonicalPartialReflect
      G sites q m hm L P sourceTag
  have hs := lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy
    G sites q m hm L sourceTag c
  have ht := lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy G sites q
    (lpReplicaPartialReflectProfile G sites m
      (profileFlux (lpReplicaCurrentGraph G sites) m P))
    ((lpReplicaSymmetrizedProfile_partialReflectCopies
      G sites m P).trans hm)
    (lpReplicaProfileOrbitLabelPartialReflectCopies
      G sites q m hm P L)
    (lpReplicaCanonicalPartialReflectToggleTag
      G sites q m hm L P sourceTag) (E c)
  have hslot : Et (E c) = Es c := by
    unfold E Es Et lpReplicaPartialReflectCanonicalCopyEquiv
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [hslot] at ht
  change lpReplicaOrbitFourColorSlotEdge G sites q targetState (Es c) =
    (E c).1 at ht
  change lpReplicaOrbitFourColorSlotEdge G sites q sourceState (Es c) =
    c.1 at hs
  rw [hstate] at ht
  by_cases hc : c ∈ P
  · have hx : Es c ∈
        lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P := by
      rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff]
      simpa only [Es, Equiv.symm_apply_apply] using hc
    rw [lpReplicaOrbitFourColorSlotEdge_crossToggle_of_mem
      G sites q _ sourceState (Es c) hx, hs] at ht
    simpa only [E, if_pos hc] using ht.symm
  · have hx : Es c ∉
        lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P := by
      intro hx
      apply hc
      rw [mem_lpReplicaOrbitCommonSlotsOfCopies_iff] at hx
      simpa only [Es, Equiv.symm_apply_apply] using hx
    rw [lpReplicaOrbitFourColorSlotEdge_crossToggle_of_not_mem
      G sites q _ sourceState (Es c) hx, hs] at ht
    simpa only [E, if_neg hc] using ht.symm


end
end StatMech.Ising
