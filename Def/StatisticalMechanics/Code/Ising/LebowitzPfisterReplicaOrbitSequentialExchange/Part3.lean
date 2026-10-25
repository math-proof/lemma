/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaPartialReflectCanonicalCopyEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    Copy (lpReplicaCurrentGraph G sites) m ≃
      Copy (lpReplicaCurrentGraph G sites)
        (lpReplicaPartialReflectProfile G sites m
          (profileFlux (lpReplicaCurrentGraph G sites) m P)) :=
  (lpReplicaProfileCopyEquivCommonSlot G sites q m hm L).trans
    (lpReplicaProfileCopyEquivCommonSlot G sites q
      (lpReplicaPartialReflectProfile G sites m
        (profileFlux (lpReplicaCurrentGraph G sites) m P))
      ((lpReplicaSymmetrizedProfile_partialReflectCopies
        G sites m P).trans hm)
      (lpReplicaProfileOrbitLabelPartialReflectCopies
        G sites q m hm P L)).symm


noncomputable def lpReplicaCanonicalPartialReflectToggleTag
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaPartialReflectProfile G sites m
        (profileFlux (lpReplicaCurrentGraph G sites) m P)) ->
      LPReplicaRowTag :=
  fun d => lpReplicaToggleRows G sites m P tag
    ((lpReplicaPartialReflectCanonicalCopyEquiv
      G sites q m hm L P).symm d)

end
end StatMech.Ising
