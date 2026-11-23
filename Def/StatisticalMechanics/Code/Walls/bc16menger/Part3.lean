/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc16menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Card
public import Theorem.StatisticalMechanics.Code.Walls.bc16menger.Part3

@[expose] public section

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
