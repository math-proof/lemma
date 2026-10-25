/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc57coarsetrif.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc54coarse
import Theorem.StatisticalMechanics.Code.Walls.bc49finiteenergy
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Def.StatisticalMechanics.Code.Walls.bc58wholebox
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc58_mem_boxInternalEdges {d k : ℕ} {x y : Site d}
    (hx : x ∈ box d k) (hy : y ∈ box d k) (hadj : (hypercubicLattice d).Adj x y) :
    s(x, y) ∈ bc58_boxInternalEdges d k := by
  classical
  unfold bc58_boxInternalEdges
  rw [Finset.mem_image]
  refine ⟨(x, y), ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨?_, ?_⟩, hadj⟩ <;> rw [Set.Finite.mem_toFinset]
  · exact hx
  · exact hy


end StatMech.Walls
