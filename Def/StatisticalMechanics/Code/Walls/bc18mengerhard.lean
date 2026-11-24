module
public import Theorem.StatisticalMechanics.Code.Walls.bc17menger.Part4
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Theorem.StatisticalMechanics.Code.Walls.bc18mengerhard


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean -/
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


def bc18_AReach (G : SimpleGraph V) (A S : Set V) : Set V :=
  {v | ∃ (a : V), a ∈ A ∧ ∃ p : G.Walk a v, ∀ z ∈ p.support, z ∈ S → z = v}

end StatMech.Walls
