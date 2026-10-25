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
import Theorem.StatisticalMechanics.Code.Walls.bc17menger.Part3


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V]


variable {G : SimpleGraph V}

def bc17_restr (G : SimpleGraph V) (W : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∈ W ∧ v ∈ W
  symm := by constructor; rintro u v ⟨h, hu, hv⟩; exact ⟨h.symm, hv, hu⟩
  loopless := ⟨fun u ⟨h, _, _⟩ => G.loopless.irrefl u h⟩

end StatMech.Walls
