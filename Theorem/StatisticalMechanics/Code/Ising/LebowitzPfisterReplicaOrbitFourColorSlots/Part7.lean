/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part7
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaOrbitFourColorSlotStateOfTag_allocation
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag).allocation =
      fun e => (L e).1 := rfl


@[simp] theorem lpReplicaOrbitFourColorSlotStateOfTag_color_copy
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m) :
    (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag).color
        ⟨lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c,
          Finset.mem_univ _⟩ =
      lpReplicaRowTagEquivFin4 (tag c) := by
  simp [lpReplicaOrbitFourColorSlotStateOfTag]

@[ext]
theorem LPReplicaOrbitFourColorSlotState.ext
    {G : SimpleGraph V} {sites : I -> V}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {s t : LPReplicaOrbitFourColorSlotState G sites q}
    (ha : s.allocation = t.allocation) (hc : s.color = t.color) : s = t := by
  cases s
  cases t
  cases ha
  cases hc
  rfl


theorem lpReplicaOrbitFourColorSlotStateOfTag_injective
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    Function.Injective
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L) := by
  intro tag₁ tag₂ hstate
  funext c
  have hcolor := congrArg
    (fun s : LPReplicaOrbitFourColorSlotState G sites q => s.color
      ⟨lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c,
        Finset.mem_univ _⟩) hstate
  simp only [lpReplicaOrbitFourColorSlotStateOfTag_color_copy] at hcolor
  exact lpReplicaRowTagEquivFin4.injective hcolor


end
end StatMech.Ising
