/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaRowTagged.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFourFunctions
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]

theorem lpReplicaRowComponent_root_mem
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) (root : LPReplicaCurrentVertex V) :
    root ∈ lpReplicaRowComponent G sites m tag row root := by
  rw [lpReplicaRowComponent, RandomCurrent.mem_compOf]
  exact Relation.ReflTransGen.refl

theorem lpReplicaRowComponent_ghost1_not_mem
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool)
    (hdisc : ¬ RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites) m)
      (lpReplicaRowCopies G sites m tag row)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
    (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉
      lpReplicaRowComponent G sites m tag row lpReplicaCurrentGhost0 := by
  rw [lpReplicaRowComponent, RandomCurrent.mem_compOf]
  exact hdisc

section Reflection

variable [Fintype I] [DecidableEq I]

theorem lpReplicaRowComponent_reflectTag
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
    (row : Bool) (root : LPReplicaCurrentVertex V) :
    lpReplicaRowComponent G sites
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
        (lpReplicaReflectTag G sites m tag) row
        (lpReplicaCurrentReflect root) =
      (lpReplicaRowComponent G sites m tag row root).map
        lpReplicaCurrentReflect.toEmbedding := by
  ext y
  have hy := lpReplicaCurrentReflect_involutive (V := V) y
  rw [← hy]
  simp only [lpReplicaRowComponent, RandomCurrent.mem_compOf]
  rw [lpReplicaRowConn_reflectTag]
  simp

end Reflection
end
end StatMech.Ising
