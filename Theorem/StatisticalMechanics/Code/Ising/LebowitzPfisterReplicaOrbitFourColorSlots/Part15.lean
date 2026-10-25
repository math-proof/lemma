/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part15
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOrbitFourColorSlotReflect_eq_reflectFamily
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (LPReplicaOrbitCommonSlot G sites q))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotReflect G sites q P s =
      lpReplicaOrbitFourColorSlotReflectFamily G sites q
        (lpReplicaOrbitFourColorSelectedStrictSlots G sites q P) s := by
  rfl


theorem lpReplicaOrbitFourColorSlotReflect_commonSlotsOfCopies
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    lpReplicaOrbitFourColorSlotReflect G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P) s =
      lpReplicaOrbitFourColorSlotReflectFamily G sites q
        (lpReplicaOrbitSpatialSelectorOfCopies G sites q m hm L P) s := by
  refine LPReplicaOrbitFourColorSlotState.ext ?_ rfl
  funext e
  change s.allocation e ∆
      lpReplicaOrbitFourColorSelectedStrictSlots G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P) e =
    s.allocation e ∆
      lpReplicaOrbitSpatialSelectorOfCopies G sites q m hm L P e
  rw [lpReplicaOrbitFourColorSelectedStrictSlots_commonSlotsOfCopies]
  rfl


theorem lpReplicaProfileOrbitLabelPartialReflectCopies_allocation_commonSlots
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
      (lpReplicaOrbitFourColorSlotReflect G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P)
        (lpReplicaOrbitFourColorSlotStateOfTag
          G sites q m hm L tag)).allocation := by
  rw [lpReplicaOrbitFourColorSlotReflect_commonSlotsOfCopies]
  exact lpReplicaProfileOrbitLabelPartialReflectCopies_allocation
    G sites q m hm L P tag


end
end StatMech.Ising
