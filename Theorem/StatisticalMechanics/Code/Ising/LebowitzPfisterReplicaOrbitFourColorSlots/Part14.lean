/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part14
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOrbitFourColorSlotReflectFamily_ofCopies_allocation
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    (lpReplicaOrbitFourColorSlotReflectFamily G sites q
      (lpReplicaOrbitSpatialSelectorOfCopies G sites q m hm L P)
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag)).allocation =
    (lpReplicaProfileOrbitSlotMove G sites q
      (lpReplicaProfileOrbitSelectedLabelEquivSlotFiber G sites q m
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m P)
        (lpReplicaProfileOrbitSelectedLabelOfCopies
          G sites q m hm P L)).1).allocation := by
  classical
  funext e
  let selected := lpReplicaProfileOrbitSelectedLabelOfCopies
    G sites q m hm P L
  let R := (selected.2 e).1.1
  let T := (selected.2 e).2.1
  have hselected : selected.1 = L := rfl
  have hR : R ⊆ (L e).1 := by
    simpa only [R, hselected] using (selected.2 e).1.2.1
  have hT : T ⊆ Finset.univ \ (L e).1 := by
    simpa only [T, hselected] using (selected.2 e).2.2.1
  change (L e).1 ∆ (R ∪ T) =
    ((selected.1 e).1 \ R) ∪ T
  rw [hselected]
  ext k
  have hTnot : k ∈ T -> k ∉ (L e).1 := by
    intro hkT
    exact (Finset.mem_sdiff.mp (hT hkT)).2
  by_cases hkL : k ∈ (L e).1 <;>
    by_cases hkR : k ∈ R <;>
      by_cases hkT : k ∈ T
  all_goals simp_all [Finset.mem_symmDiff]
  exact hkL (hR hkR)


theorem lpReplicaProfileOrbitLabelPartialReflectCopies_allocation
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    (fun e => ((lpReplicaProfileOrbitLabelPartialReflectCopies
      G sites q m hm P L) e).1) =
      (lpReplicaOrbitFourColorSlotReflectFamily G sites q
        (lpReplicaOrbitSpatialSelectorOfCopies G sites q m hm L P)
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m hm L tag)).allocation := by
  rw [lpReplicaOrbitFourColorSlotReflectFamily_ofCopies_allocation]
  rfl


theorem lpReplicaOrbitFourColorSlotReflectFamily_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : forall e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
      Finset (Fin (q e.1))) :
    Function.Involutive
      (lpReplicaOrbitFourColorSlotReflectFamily G sites q P) := by
  intro s
  apply LPReplicaOrbitFourColorSlotState.ext
  · funext e
    simp [lpReplicaOrbitFourColorSlotReflectFamily]
  · rfl


end
end StatMech.Ising
