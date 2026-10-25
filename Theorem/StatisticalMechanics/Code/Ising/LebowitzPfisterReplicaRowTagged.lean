/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFourFunctions
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]

section Reflection

variable [Fintype I] [DecidableEq I]


theorem lpReplicaRowCopies_reflectTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) :
    lpReplicaRowCopies G sites
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
        (lpReplicaReflectTag G sites m tag) row =
      lpReplicaReflectCopies G sites m
        (lpReplicaRowCopies G sites m tag row) := by
  ext c
  simp [lpReplicaRowCopies, lpReplicaReflectTag]

theorem lpReplicaCurrentCopies_reflectTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    lpReplicaCurrentCopies G sites
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
        (lpReplicaReflectTag G sites m tag) row current =
      lpReplicaReflectCopies G sites m
        (lpReplicaCurrentCopies G sites m tag row current) := by
  ext c
  simp [lpReplicaCurrentCopies, lpReplicaReflectTag]

theorem lpReplicaCurrentSources_reflectTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row current : Bool) :
    RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaCurrentCopies G sites
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
          (lpReplicaReflectTag G sites m tag) row current) =
      (RandomCurrent.sources
        (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaCurrentCopies G sites m tag row current)).map
          lpReplicaCurrentReflect.toEmbedding := by
  rw [lpReplicaCurrentCopies_reflectTag,
    lpReplicaReflectCopies_sources]

theorem lpReplicaRowConn_reflectTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) (a b : LPReplicaCurrentVertex V) :
    RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaRowCopies G sites
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
          (lpReplicaReflectTag G sites m tag) row)
        (lpReplicaCurrentReflect a) (lpReplicaCurrentReflect b) ↔
      RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) m)
        (lpReplicaRowCopies G sites m tag row) a b := by
  rw [lpReplicaRowCopies_reflectTag]
  exact lpReplicaReflectCopies_connK G sites m _ a b

end Reflection
end
end StatMech.Ising
