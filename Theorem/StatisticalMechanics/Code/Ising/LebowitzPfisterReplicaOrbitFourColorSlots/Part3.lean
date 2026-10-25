/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaProfileOrbitPairedCoordEquivSlot_apply_left_mem
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))
    (k : Fin (m e.1)) :
    lpReplicaProfileOrbitPairedCoordEquivSlot G sites q m hm L e
        (Sum.inl k) ∈ (L e).1 := by
  classical
  simp [lpReplicaProfileOrbitPairedCoordEquivSlot]

@[simp] theorem lpReplicaProfileOrbitPairedCoordEquivSlot_apply_right_not_mem
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))
    (k : Fin (m (lpReplicaCurrentEdgeReflect G sites e.1))) :
    lpReplicaProfileOrbitPairedCoordEquivSlot G sites q m hm L e
        (Sum.inr k) ∉ (L e).1 := by
  classical
  have hleft : (L e).1.card = m e.1 :=
    (Finset.mem_powersetCard.mp (L e).2).2
  have hright : (Finset.univ \ (L e).1).card =
      m (lpReplicaCurrentEdgeReflect G sites e.1) := by
    have hq := congrFun hm e.1
    unfold lpReplicaSymmetrizedProfile at hq
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin, hleft]
    omega
  change (((Finset.univ \ (L e).1).orderIsoOfFin hright) k).1 ∉ (L e).1
  exact (Finset.mem_sdiff.mp
    (((Finset.univ \ (L e).1).orderIsoOfFin hright) k).2).2


end
end StatMech.Ising
