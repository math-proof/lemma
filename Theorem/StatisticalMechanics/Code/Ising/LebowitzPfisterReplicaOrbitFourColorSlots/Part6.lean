/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part6
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaOrbitProfileCoordEquivCommonSlot_fixed
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites))
    (k : Fin (m e.1)) :
    lpReplicaOrbitProfileCoordEquivCommonSlot G sites q m hm L
        ⟨Sum.inl e, k⟩ =
      Sum.inl ⟨e, Equiv.cast (congrArg Fin
        (lpReplicaProfile_eq_half_of_fixed G sites q m hm e)) k⟩ := by
  rfl

@[simp] theorem lpReplicaOrbitProfileCoordEquivCommonSlot_strict
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))
    (k : Fin (m e.1)) :
    lpReplicaOrbitProfileCoordEquivCommonSlot G sites q m hm L
        ⟨Sum.inr (Sum.inl e), k⟩ =
      Sum.inr ⟨e,
        lpReplicaProfileOrbitPairedCoordEquivSlot G sites q m hm L e
          (Sum.inl k)⟩ := by
  rfl

@[simp] theorem lpReplicaOrbitProfileCoordEquivCommonSlot_reflectStrict
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))
    (k : Fin (m (lpReplicaCurrentEdgeReflect G sites e.1))) :
    lpReplicaOrbitProfileCoordEquivCommonSlot G sites q m hm L
        ⟨Sum.inr (Sum.inr e), k⟩ =
      Sum.inr ⟨e,
        lpReplicaProfileOrbitPairedCoordEquivSlot G sites q m hm L e
          (Sum.inr k)⟩ := by
  rfl


@[simp] theorem lpReplicaProfileCopyEquivCommonSlot_strict
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))
    (k : Fin (m e.1)) :
    lpReplicaProfileCopyEquivCommonSlot G sites q m hm L ⟨e.1, k⟩ =
      Sum.inr ⟨e,
        lpReplicaProfileOrbitLabelRepEmbedding G sites q m L e k⟩ := by
  classical
  have hnotFixed : e.1 ∉ lpReplicaCurrentEdgeOrbitFixed G sites := by
    intro hfixed
    exact ((mem_lpReplicaCurrentEdgeOrbitStrictReps G sites e.1).1 e.2).2
      ((mem_lpReplicaCurrentEdgeOrbitFixed G sites e.1).1 hfixed)
  let d := lpReplicaProfileCopyEquivOrbitCoord G sites m ⟨e.1, k⟩
  have hdFst : d.1 = Sum.inr (Sum.inl e) := by
    dsimp only [d]
    rw [lpReplicaProfileCopyEquivOrbitCoord_fst]
    apply (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm.injective
    simp
  have hdVal : d.2.1 = k.1 := by
    simpa only [d] using
      lpReplicaProfileCopyEquivOrbitCoord_snd_val G sites m ⟨e.1, k⟩
  change lpReplicaOrbitProfileCoordEquivCommonSlot
      G sites q m hm L d = _
  rcases d with ⟨de, dk⟩
  dsimp only at hdFst hdVal
  subst de
  have hdk : dk = k := Fin.ext hdVal
  subst dk
  rw [lpReplicaOrbitProfileCoordEquivCommonSlot_strict]
  rfl


@[simp] theorem lpReplicaProfileCopyEquivCommonSlot_reflectStrict
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))
    (k : Fin (m (lpReplicaCurrentEdgeReflect G sites e.1))) :
    lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
        ⟨lpReplicaCurrentEdgeReflect G sites e.1, k⟩ =
      Sum.inr ⟨e,
        lpReplicaProfileOrbitLabelReflectEmbedding
          G sites q m hm L e k⟩ := by
  classical
  have hnotFixed : lpReplicaCurrentEdgeReflect G sites e.1 ∉
      lpReplicaCurrentEdgeOrbitFixed G sites := by
    intro hfixed
    have heq := (mem_lpReplicaCurrentEdgeOrbitFixed G sites _).1 hfixed
    have heq' : lpReplicaCurrentEdgeReflect G sites e.1 = e.1 := by
      rw [lpReplicaCurrentEdgeReflect_involutive] at heq
      exact heq
    exact ((mem_lpReplicaCurrentEdgeOrbitStrictReps G sites e.1).1 e.2).2
      heq'.symm
  have hnotStrict : lpReplicaCurrentEdgeReflect G sites e.1 ∉
      lpReplicaCurrentEdgeOrbitStrictReps G sites := by
    intro hstrict
    have hrep := (mem_lpReplicaCurrentEdgeOrbitStrictReps G sites e.1).1 e.2
    have href := (mem_lpReplicaCurrentEdgeOrbitStrictReps G sites
      (lpReplicaCurrentEdgeReflect G sites e.1)).1 hstrict
    exact hrep.2
      (lpReplicaCurrentEdge_eq_reflect_of_mem_reps_of_reflect_mem_reps
        G sites e.1 hrep.1 (by
          simpa only [lpReplicaCurrentEdgeReflect_involutive] using href.1))
  let d := lpReplicaProfileCopyEquivOrbitCoord G sites m
    ⟨lpReplicaCurrentEdgeReflect G sites e.1, k⟩
  have hdFst : d.1 = Sum.inr (Sum.inr e) := by
    dsimp only [d]
    rw [lpReplicaProfileCopyEquivOrbitCoord_fst]
    apply (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm.injective
    simp
  have hdVal : d.2.1 = k.1 := by
    simpa only [d] using
      lpReplicaProfileCopyEquivOrbitCoord_snd_val G sites m
        ⟨lpReplicaCurrentEdgeReflect G sites e.1, k⟩
  change lpReplicaOrbitProfileCoordEquivCommonSlot
      G sites q m hm L d = _
  rcases d with ⟨de, dk⟩
  dsimp only at hdFst hdVal
  subst de
  have hdk : dk = k := Fin.ext hdVal
  subst dk
  rw [lpReplicaOrbitProfileCoordEquivCommonSlot_reflectStrict]
  rfl


end
end StatMech.Ising
