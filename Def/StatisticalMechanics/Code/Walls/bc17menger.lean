/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc16menger.Part4
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V]


def bc17_familyMapLe {G G' : SimpleGraph V} (hGG' : G' ≤ G) {A B : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G' A B ι) : bc16_DisjointPathFamily G A B ι where
  a := F.a
  b := F.b
  p := fun i => (F.p i).mapLe hGG'
  ha := F.ha
  hb := F.hb
  hp := fun i => (Walk.mapLe_isPath hGG').2 (F.hp i)
  hdisj := by
    intro i j hij x hx hx'
    rw [Walk.support_mapLe_eq_support] at hx hx'
    exact F.hdisj hij hx hx'


end StatMech.Walls
