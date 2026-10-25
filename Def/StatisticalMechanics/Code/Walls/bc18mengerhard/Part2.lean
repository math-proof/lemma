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
import Theorem.StatisticalMechanics.Code.Walls.bc18mengerhard.Part2


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V]

variable {G : SimpleGraph V}


def bc18_walkToRestrCompl {Y : Set V} {a b : V} (p : G.Walk a b)
    (hp : ∀ w ∈ p.support, w ∉ Y) : (bc17_restr G {v | v ∉ Y}).Walk a b :=
  p.transfer _ (by
    intro e he
    obtain ⟨w₁, w₂⟩ := e
    rw [mem_edgeSet, bc17_restr_adj]
    exact ⟨p.adj_of_mem_edges he,
      hp _ (p.fst_mem_support_of_mem_edges he), hp _ (p.snd_mem_support_of_mem_edges he)⟩)


end StatMech.Walls
