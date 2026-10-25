/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Theorem.StatisticalMechanics.Code.Walls.bc16menger.Part3


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}


def bc16_singletonFamily {S T : Set V} {s t : V} (hs : s ∈ S) (ht : t ∈ T)
    {p : G.Walk s t} (hp : p.IsPath) : bc16_DisjointPathFamily G S T (PUnit.{1}) where
  a := fun _ => s
  b := fun _ => t
  p := fun _ => p
  ha := fun _ => hs
  hb := fun _ => ht
  hp := fun _ => hp
  hdisj := by
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij


end StatMech.Walls
