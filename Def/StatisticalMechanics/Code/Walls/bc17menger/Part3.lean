module
public import Theorem.StatisticalMechanics.Code.Walls.bc16menger.Part4
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Theorem.StatisticalMechanics.Code.Walls.bc17menger.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc17menger.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V]


variable {G : SimpleGraph V}

def bc17_HardDir (G : SimpleGraph V) (A B : Set V) : Prop :=
  ∀ k : ℕ, (∀ C, bc16_IsSeparator G A B C → k ≤ C.ncard) →
    Nonempty (bc16_DisjointPathFamily G A B (Fin k))


end StatMech.Walls
