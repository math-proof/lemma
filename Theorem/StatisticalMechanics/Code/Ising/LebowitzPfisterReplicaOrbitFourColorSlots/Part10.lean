/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part10
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem mem_lpReplicaOrbitCommonSlotsOfCopies_iff
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (x : LPReplicaOrbitCommonSlot G sites q) :
    x ∈ lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P ↔
      (lpReplicaProfileCopyEquivCommonSlot G sites q m hm L).symm x ∈ P := by
  classical
  simp [lpReplicaOrbitCommonSlotsOfCopies]


theorem lpReplicaOrbitFourColorSlotRowToggle_stateOfTag
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaOrbitFourColorSlotRowToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
        (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) =
      lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L
        (lpReplicaToggleRows G sites m P tag) := by
  apply LPReplicaOrbitFourColorSlotState.ext
  · rfl
  · funext x
    let E := lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
    let c := E.symm x.1
    have hx : x.1 ∈ lpReplicaOrbitCommonSlotsOfCopies
        G sites q m hm L P ↔ c ∈ P := by
      exact mem_lpReplicaOrbitCommonSlotsOfCopies_iff
        G sites q m hm L P x.1
    change (if x.1 ∈ lpReplicaOrbitCommonSlotsOfCopies
          G sites q m hm L P then
        lpReplicaRowToggleFin4
          (lpReplicaRowTagEquivFin4 (tag c))
      else lpReplicaRowTagEquivFin4 (tag c)) =
      lpReplicaRowTagEquivFin4
        (if c ∈ P then (!(tag c).1, (tag c).2) else tag c)
    by_cases hc : c ∈ P
    · rw [if_pos (hx.mpr hc), if_pos hc]
      rcases htag : tag c with ⟨row, current⟩
      cases row <;> cases current <;> rfl
    · rw [if_neg (fun h => hc (hx.mp h)), if_neg hc]


end
end StatMech.Ising
