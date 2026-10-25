/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutHallExact
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagProjection
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOrientedFourColorSlotState_ofRowGate
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hgate : LPReplicaRowGate G sites m A B tag)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    lpReplicaOrientedFourColorSlotState G sites A
        (B.map lpReplicaCurrentReflect.toEmbedding) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A
          (B.map lpReplicaCurrentReflect.toEmbedding) q
          (lpReplicaDecoratedOrbitAtomOfRowGate
            G sites m q tag A B hm hgate L)) =
      lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag := by
  unfold lpReplicaOrientedFourColorSlotState
  rw [lpReplicaOrientedFourColorTag_ofRowGate]
  rfl


theorem lpReplicaOrbitFourColorSlotStateOfTag_cast_profile
    (G : SimpleGraph V) (sites : I -> V)
    (q m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (h : n = m)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hn : lpReplicaSymmetrizedProfile G sites n = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (tag : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
    lpReplicaOrbitFourColorSlotStateOfTag G sites q n hn
        (cast (congrArg (LPReplicaProfileOrbitLabel G sites q) h.symm) L)
        (fun c => tag (cast (congrArg
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites)) h) c)) =
      lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag := by
  subst n
  rfl


end
end StatMech.Ising
