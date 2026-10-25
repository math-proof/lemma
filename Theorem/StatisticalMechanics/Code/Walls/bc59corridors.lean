/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc59corridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc58wholebox.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc49finiteenergy
import Def.StatisticalMechanics.Code.Walls.bc59corridors
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc59_corridors_give_trifurcation (ω : ConfigSpace (Sym2 (Site d)))
    (h : bc59_DisjointCorridors ω) :
    ∃ G : Finset (Sym2 (Site d)), bc47_IsClassicalTrifurcation (forceOpenFinset G ω) 0 := by
  obtain ⟨G, a₁, a₂, a₃, hne, ⟨hG1, hG2, hG3⟩, ⟨hadj1, hadj2, hadj3⟩,
    ⟨hi1, hi2, hi3⟩, ⟨hs12, hs13, hs23⟩⟩ := h
  refine ⟨G, a₁, a₂, a₃, hne, ⟨?_, ?_, ?_⟩, ⟨hi1, hi2, hi3⟩, ⟨hs12, hs13, hs23⟩⟩
  · exact ⟨hadj1, forceOpenFinset_of_mem hG1 ω⟩
  · exact ⟨hadj2, forceOpenFinset_of_mem hG2 ω⟩
  · exact ⟨hadj3, forceOpenFinset_of_mem hG3 ω⟩


end StatMech.Walls
