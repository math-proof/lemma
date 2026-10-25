/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part18
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotCrossNormalize G sites q
        (lpReplicaOrbitFourColorSlotCrossToggle G sites q P s) =
      lpReplicaOrbitFourColorSlotCrossNormalize G sites q s := by
  rw [lpReplicaOrbitFourColorSlotCrossNormalize,
    lpReplicaOrbitFourColorSlotRowMask_crossToggle,
    lpReplicaOrbitFourColorSlotCrossToggle_comp]
  unfold lpReplicaOrbitFourColorSlotCrossNormalize
  congr 1
  ext x
  simp


theorem lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitFourColorSlotRowMask G sites q s)
        (lpReplicaOrbitFourColorSlotCrossNormalize G sites q s) = s := by
  exact lpReplicaOrbitFourColorSlotCrossToggle_involutive G sites q
    (lpReplicaOrbitFourColorSlotRowMask G sites q s) s


theorem lpReplicaOrbitFourColorSlotState_eq_iff_crossNormalize_eq_and_rowMask_eq
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s t : LPReplicaOrbitFourColorSlotState G sites q) :
    s = t ↔
      lpReplicaOrbitFourColorSlotCrossNormalize G sites q s =
          lpReplicaOrbitFourColorSlotCrossNormalize G sites q t ∧
        lpReplicaOrbitFourColorSlotRowMask G sites q s =
          lpReplicaOrbitFourColorSlotRowMask G sites q t := by
  constructor
  · intro h
    exact ⟨congrArg (lpReplicaOrbitFourColorSlotCrossNormalize G sites q) h,
      congrArg (lpReplicaOrbitFourColorSlotRowMask G sites q) h⟩
  · rintro ⟨hnorm, hrow⟩
    calc
      s = lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitFourColorSlotRowMask G sites q s)
          (lpReplicaOrbitFourColorSlotCrossNormalize G sites q s) :=
        (lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize
          G sites q s).symm
      _ = lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (lpReplicaOrbitFourColorSlotRowMask G sites q t)
          (lpReplicaOrbitFourColorSlotCrossNormalize G sites q t) := by
        rw [hrow, hnorm]
      _ = t := lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize
        G sites q t


theorem lpReplicaOrbitFourColorSlotCrossToggle_eq_iff
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P Q : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s t : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotCrossToggle G sites q P s =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q Q t ↔
      lpReplicaOrbitFourColorSlotCrossNormalize G sites q s =
          lpReplicaOrbitFourColorSlotCrossNormalize G sites q t ∧
        lpReplicaOrbitFourColorSlotRowMask G sites q s ∆ P =
          lpReplicaOrbitFourColorSlotRowMask G sites q t ∆ Q := by
  rw [lpReplicaOrbitFourColorSlotState_eq_iff_crossNormalize_eq_and_rowMask_eq,
    lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle,
    lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle,
    lpReplicaOrbitFourColorSlotRowMask_crossToggle,
    lpReplicaOrbitFourColorSlotRowMask_crossToggle]


theorem exists_crossToggle_eq_iff_crossNormalize_eq
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s t : LPReplicaOrbitFourColorSlotState G sites q) :
    (∃ P : Finset (LPReplicaOrbitCommonSlot G sites q),
        t = lpReplicaOrbitFourColorSlotCrossToggle G sites q P s) ↔
      lpReplicaOrbitFourColorSlotCrossNormalize G sites q t =
        lpReplicaOrbitFourColorSlotCrossNormalize G sites q s := by
  constructor
  · rintro ⟨P, rfl⟩
    exact lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle
      G sites q P s
  · intro hnorm
    let Rs := lpReplicaOrbitFourColorSlotRowMask G sites q s
    let Rt := lpReplicaOrbitFourColorSlotRowMask G sites q t
    refine ⟨Rt ∆ Rs, ?_⟩
    have h := congrArg
      (lpReplicaOrbitFourColorSlotCrossToggle G sites q Rt) hnorm
    change lpReplicaOrbitFourColorSlotCrossToggle G sites q Rt
        (lpReplicaOrbitFourColorSlotCrossToggle G sites q Rt t) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q Rt
        (lpReplicaOrbitFourColorSlotCrossToggle G sites q Rs s) at h
    rw [lpReplicaOrbitFourColorSlotCrossToggle_involutive,
      lpReplicaOrbitFourColorSlotCrossToggle_comp] at h
    exact h


theorem lpReplicaOrbitFourColorSlotBranchedCrossToggle_injective_of_collisionStable
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    {α β : Type*}
    (encode : α -> LPReplicaOrbitFourColorSlotState G sites q)
    (selector : α -> Finset (LPReplicaOrbitCommonSlot G sites q))
    (branch : α -> β)
    (hencode : Function.Injective encode)
    (hstable : forall a b,
      (branch a, lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (selector a) (encode a)) =
        (branch b, lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (selector b) (encode b)) ->
      selector a = selector b) :
    Function.Injective fun a =>
      (branch a, lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (selector a) (encode a)) := by
  intro a b hab
  have hselector : selector a = selector b := hstable a b hab
  have himage :
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (selector a) (encode a) =
        lpReplicaOrbitFourColorSlotCrossToggle G sites q
          (selector b) (encode b) := congrArg Prod.snd hab
  apply hencode
  have himage' : lpReplicaOrbitFourColorSlotCrossToggle G sites q
      (selector b) (encode a) =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (selector b) (encode b) := by
    simpa only [hselector] using himage
  have hinv := congrArg
    (lpReplicaOrbitFourColorSlotCrossToggle G sites q (selector b))
    himage'
  rw [lpReplicaOrbitFourColorSlotCrossToggle_involutive
      G sites q (selector b) (encode a),
    lpReplicaOrbitFourColorSlotCrossToggle_involutive
      G sites q (selector b) (encode b)] at hinv
  exact hinv


theorem lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_allocation
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    (lpReplicaOrbitFourColorSlotCrossToggle G sites q
      (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
      (lpReplicaOrbitFourColorSlotStateOfTag
        G sites q m hm L tag)).allocation =
      fun e => ((lpReplicaProfileOrbitLabelPartialReflectCopies
        G sites q m hm P L) e).1 := by
  symm
  exact lpReplicaProfileOrbitLabelPartialReflectCopies_allocation_commonSlots
    G sites q m hm L P tag


theorem lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_color
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    (lpReplicaOrbitFourColorSlotCrossToggle G sites q
      (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
      (lpReplicaOrbitFourColorSlotStateOfTag
        G sites q m hm L tag)).color =
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L
        (lpReplicaToggleRows G sites m P tag)).color := by
  change (lpReplicaOrbitFourColorSlotRowToggle G sites q
      (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
      (lpReplicaOrbitFourColorSlotStateOfTag
        G sites q m hm L tag)).color = _
  rw [lpReplicaOrbitFourColorSlotRowToggle_stateOfTag]


theorem lpReplicaOrbitFourColorSlotEdge_reflect_strict
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))
    (k : Fin (q e.1)) :
    lpReplicaOrbitFourColorSlotEdge G sites q
        (lpReplicaOrbitFourColorSlotReflect G sites q P s)
        (Sum.inr ⟨e, k⟩) =
      if (Sum.inr ⟨e, k⟩ : LPReplicaOrbitCommonSlot G sites q) ∈ P then
        lpReplicaCurrentEdgeReflect G sites
          (lpReplicaOrbitFourColorSlotEdge G sites q s (Sum.inr ⟨e, k⟩))
      else lpReplicaOrbitFourColorSlotEdge G sites q s (Sum.inr ⟨e, k⟩) := by
  classical
  by_cases hp : (Sum.inr ⟨e, k⟩ :
      LPReplicaOrbitCommonSlot G sites q) ∈ P <;>
    by_cases ha : k ∈ s.allocation e
  all_goals
    simp [lpReplicaOrbitFourColorSlotEdge,
      lpReplicaOrbitFourColorSlotReflect,
      lpReplicaOrbitFourColorSelectedStrictSlots,
      Finset.mem_symmDiff, hp, ha]
  exact (lpReplicaCurrentEdgeReflect_involutive G sites e.1).symm


end
end StatMech.Ising
