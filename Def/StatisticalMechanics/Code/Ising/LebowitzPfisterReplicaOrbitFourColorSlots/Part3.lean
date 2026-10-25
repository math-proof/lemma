/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaProfileOrbitPairedCoordEquivSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) :
    Fin (m e.1) ⊕
        Fin (m (lpReplicaCurrentEdgeReflect G sites e.1)) ≃
      Fin (q e.1) := by
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
  let left : Fin (m e.1) ≃ {x : Fin (q e.1) // x ∈ (L e).1} :=
    (L e).1.orderIsoOfFin hleft
  let right0 : Fin (m (lpReplicaCurrentEdgeReflect G sites e.1)) ≃
      {x : Fin (q e.1) // x ∈ Finset.univ \ (L e).1} :=
    (Finset.univ \ (L e).1).orderIsoOfFin hright
  let rightCast : {x : Fin (q e.1) // x ∈ Finset.univ \ (L e).1} ≃
      {x : Fin (q e.1) // x ∉ (L e).1} := {
    toFun x := ⟨x.1, (Finset.mem_sdiff.mp x.2).2⟩
    invFun x := ⟨x.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, x.2⟩⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
  }
  exact (Equiv.sumCongr left (right0.trans rightCast)).trans
    (Equiv.sumCompl fun x : Fin (q e.1) => x ∈ (L e).1)

end
end StatMech.Ising
