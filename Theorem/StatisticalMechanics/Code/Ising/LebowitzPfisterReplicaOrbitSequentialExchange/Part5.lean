/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaPartialReflectCanonicalRelabelEquiv_ends
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (d : Copy (lpReplicaCurrentGraph G sites)
      (lpReplicaCollisionProfile G sites
        (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
        (profileFlux (lpReplicaCurrentGraph G sites) m P))) :
    endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaPartialReflectProfile G sites m
          (profileFlux (lpReplicaCurrentGraph G sites) m P))
        (lpReplicaPartialReflectCanonicalRelabelEquiv
          G sites q m hm L P d) =
      endsM (lpReplicaCurrentGraph G sites)
        (lpReplicaCollisionProfile G sites
          (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P))
          (profileFlux (lpReplicaCurrentGraph G sites) m P)) d := by
  let c := (lpReplicaPartialReflectCopyEquivRaw G sites m P).symm d
  have hcanon := lpReplicaPartialReflectCanonicalCopyEquiv_edge
    G sites q m hm L P c
  have hraw := lpReplicaPartialReflectCopyEquivRaw_edge G sites m P c
  have hd : lpReplicaPartialReflectCopyEquivRaw G sites m P c = d := by
    exact (lpReplicaPartialReflectCopyEquivRaw G sites m P).apply_symm_apply d
  change (lpReplicaPartialReflectCanonicalCopyEquiv
    G sites q m hm L P c).1.1 = d.1.1
  rw [<- hd]
  exact congrArg Subtype.val (hcanon.trans hraw.symm)

end
end StatMech.Ising
