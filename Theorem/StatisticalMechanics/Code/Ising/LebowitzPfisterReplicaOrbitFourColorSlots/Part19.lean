/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part19
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOrbitFourColorSlotLeftPattern_stateOfTag
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (u v : LPReplicaCurrentVertex V)
    (hleft : LeftPattern
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m) Finset.univ
      A B u v (lpReplicaTagFourColor G sites m tag)) :
    LPReplicaOrbitFourColorSlotLeftPattern G sites q A B u v
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) := by
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
  let s := lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag
  have htransport := leftPattern_lpReplicaFourColorTransport E
    (StatMech.Sharpness.FluxEdgeCopy.endsM
      (lpReplicaCurrentGraph G sites) m)
    (lpReplicaOrbitFourColorSlotEnds G sites q s)
    (lpReplicaOrbitFourColorSlotEnds_stateOfTag_copy
      G sites q m hm L tag) A B u v
    (lpReplicaTagFourColor G sites m tag) hleft
  simpa only [LPReplicaOrbitFourColorSlotLeftPattern, s, E,
    lpReplicaFourColorTransport, lpReplicaOrbitFourColorSlotStateOfTag,
    lpReplicaTagFourColor] using htransport


theorem lpReplicaOrbitFourColorSlotLeftPattern_partialReflectCopies
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (tag' : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites)
        (lpReplicaPartialReflectProfile G sites m
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m P)) -> LPReplicaRowTag)
    (A B : Finset (LPReplicaCurrentVertex V))
    (u v : LPReplicaCurrentVertex V)
    (hleft : LeftPattern
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites)
          (lpReplicaPartialReflectProfile G sites m
            (StatMech.Sharpness.FluxEdgeCopy.profileFlux
              (lpReplicaCurrentGraph G sites) m P)))
      Finset.univ A B u v
      (lpReplicaTagFourColor G sites
        (lpReplicaPartialReflectProfile G sites m
          (StatMech.Sharpness.FluxEdgeCopy.profileFlux
            (lpReplicaCurrentGraph G sites) m P)) tag')) :
    let m' := lpReplicaPartialReflectProfile G sites m
      (StatMech.Sharpness.FluxEdgeCopy.profileFlux
        (lpReplicaCurrentGraph G sites) m P)
    let hm' : lpReplicaSymmetrizedProfile G sites m' = q :=
      (lpReplicaSymmetrizedProfile_partialReflect G sites m
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m P)
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux_le
          (lpReplicaCurrentGraph G sites) m P)).trans hm
    let L' := lpReplicaProfileOrbitLabelPartialReflectCopies
      G sites q m hm P L
    let s' := lpReplicaOrbitFourColorSlotStateOfTag
      G sites q m' hm' L' tag'
    s'.allocation =
        (lpReplicaOrbitFourColorSlotReflectFamily G sites q
          (lpReplicaOrbitSpatialSelectorOfCopies G sites q m hm L P)
          (lpReplicaOrbitFourColorSlotStateOfTag
            G sites q m hm L tag)).allocation ∧
      LPReplicaOrbitFourColorSlotLeftPattern G sites q A B u v s' := by
  dsimp only
  constructor
  · simpa only [lpReplicaOrbitFourColorSlotStateOfTag_allocation] using
      lpReplicaProfileOrbitLabelPartialReflectCopies_allocation
        G sites q m hm L P tag
  · exact lpReplicaOrbitFourColorSlotLeftPattern_stateOfTag
      G sites q _ _ _ tag' A B u v hleft


end
end StatMech.Ising
