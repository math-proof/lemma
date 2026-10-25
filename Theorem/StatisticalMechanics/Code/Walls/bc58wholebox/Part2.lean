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
import Def.StatisticalMechanics.Code.Walls.bc58wholebox.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc58_boxOpen_edge_open {d k : ℕ} {x y : Site d}
    (hx : x ∈ box d k) (hy : y ∈ box d k) (hadj : (hypercubicLattice d).Adj x y)
    (ω : ConfigSpace (Sym2 (Site d))) :
    IsOpenEdge d (bc58_boxOpen d k ω) x y :=
  ⟨hadj, forceOpenFinset_of_mem (bc58_mem_boxInternalEdges hx hy hadj) ω⟩


theorem bc58_boxOpen_adj_connected {d k : ℕ} {x y : Site d}
    (hx : x ∈ box d k) (hy : y ∈ box d k) (hadj : (hypercubicLattice d).Adj x y)
    (ω : ConfigSpace (Sym2 (Site d))) :
    Connected d (bc58_boxOpen d k ω) x y :=
  IsOpenEdge.connected (bc58_boxOpen_edge_open hx hy hadj ω)


theorem bc58_boxOpen_removeSite_edge_open {d k : ℕ} {x y : Site d}
    (hx : x ∈ box d k) (hy : y ∈ box d k) (hadj : (hypercubicLattice d).Adj x y)
    (h0 : (0 : Site d) ∉ s(x, y)) (ω : ConfigSpace (Sym2 (Site d))) :
    IsOpenEdge d (removeSite 0 (bc58_boxOpen d k ω)) x y := by
  refine ⟨hadj, ?_⟩
  rw [removeSite_apply_of_notMem h0]
  exact forceOpenFinset_of_mem (bc58_mem_boxInternalEdges hx hy hadj) ω


theorem bc58_boxOpen_removeSite_adj_connected {d k : ℕ} {x y : Site d}
    (hx : x ∈ box d k) (hy : y ∈ box d k) (hadj : (hypercubicLattice d).Adj x y)
    (h0 : (0 : Site d) ∉ s(x, y)) (ω : ConfigSpace (Sym2 (Site d))) :
    Connected d (removeSite 0 (bc58_boxOpen d k ω)) x y :=
  IsOpenEdge.connected (bc58_boxOpen_removeSite_edge_open hx hy hadj h0 ω)


end StatMech.Walls
