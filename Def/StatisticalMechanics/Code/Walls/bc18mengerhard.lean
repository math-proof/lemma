/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc18mengerhard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc17menger.Part4
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Theorem.StatisticalMechanics.Code.Walls.bc18mengerhard


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V]

variable {G : SimpleGraph V}


def bc18_AReach (G : SimpleGraph V) (A S : Set V) : Set V :=
  {v | ∃ (a : V), a ∈ A ∧ ∃ p : G.Walk a v, ∀ z ∈ p.support, z ∈ S → z = v}

end StatMech.Walls
