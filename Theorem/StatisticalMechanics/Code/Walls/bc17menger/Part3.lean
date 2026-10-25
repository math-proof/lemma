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
import Def.StatisticalMechanics.Code.Walls.bc17menger.Part3


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V]


variable {G : SimpleGraph V}

theorem bc17_hardDir_bot [Fintype V] (A B : Set V) :
    bc17_HardDir (⊥ : SimpleGraph V) A B :=
  fun _ hmin => bc17_hard_bot A B hmin


theorem bc17_hardDir_step_case1 {G : SimpleGraph V} {A B : Set V} {x y : V} {k : ℕ}
    (hH : bc17_HardDir (G.deleteEdges {s(x, y)}) A B)
    (hC1 : ∀ C, bc16_IsSeparator (G.deleteEdges {s(x, y)}) A B C → k ≤ C.ncard) :
    Nonempty (bc16_DisjointPathFamily G A B (Fin k)) := by
  obtain ⟨F⟩ := hH k hC1
  exact ⟨bc17_familyMapLe (deleteEdges_le _) F⟩


end StatMech.Walls
