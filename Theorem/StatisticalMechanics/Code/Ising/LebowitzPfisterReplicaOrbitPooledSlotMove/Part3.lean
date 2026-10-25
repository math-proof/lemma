/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledSlotMove.Part3
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaPooledSelectedSlotStateOfCopies_profile
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    (lpReplicaPooledSelectedSlotStateOfCopies
      G sites m q hm P L).profile = m := rfl

@[simp] theorem lpReplicaPooledSelectedSlotStateOfCopies_selected
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    (lpReplicaPooledSelectedSlotStateOfCopies
      G sites m q hm P L).selected =
        StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m P := rfl


@[simp] theorem lpReplicaPooledSelectedSlotMove_ofCopies_profile
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    (lpReplicaPooledSelectedSlotMove G sites q
      (lpReplicaPooledSelectedSlotStateOfCopies
        G sites m q hm P L)).profile =
      lpReplicaPartialReflectProfile G sites m
        (StatMech.Sharpness.FluxEdgeCopy.profileFlux
          (lpReplicaCurrentGraph G sites) m P) := rfl


@[simp] theorem lpReplicaPooledSelectedSlotMove_ofCopies_orbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    ((lpReplicaPooledSelectedOrbitLabelEquivSlotState G sites q).symm
      (lpReplicaPooledSelectedSlotMove G sites q
        (lpReplicaPooledSelectedSlotStateOfCopies
          G sites m q hm P L))).2.2.1 =
      lpReplicaProfileOrbitLabelPartialReflectCopies
        G sites q m hm P L := rfl

theorem lpReplicaPooledSelectedSlotMove_injective
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Injective (lpReplicaPooledSelectedSlotMove G sites q) :=
  (lpReplicaPooledSelectedSlotMoveEquiv G sites q).injective


theorem card_image_lpReplicaPooledSelectedSlotMove
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (LPReplicaPooledSelectedSlotState G sites q)) :
    (S.image (lpReplicaPooledSelectedSlotMove G sites q)).card = S.card := by
  classical
  exact Finset.card_image_of_injective S
    (lpReplicaPooledSelectedSlotMove_injective G sites q)


theorem lpReplicaPooledSelectedSlotMove_hall
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (LPReplicaPooledSelectedSlotState G sites q)) :
    S.card <= (S.biUnion fun z =>
      {lpReplicaPooledSelectedSlotMove G sites q z}).card := by
  classical
  rw [Finset.biUnion_singleton]
  exact (card_image_lpReplicaPooledSelectedSlotMove G sites q S).ge

end
end StatMech.Ising
