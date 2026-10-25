/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/atsattachsurgery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsBoundaryConnected.Part4
import Theorem.StatisticalMechanics.Code.Walls.pc2boundaryconn.Part4
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem ats_mem_insert_of_ne {K : Finset (Site 2)} {c x : Site 2} (hx : x ≠ c) :
    x ∈ (↑(insert c K) : Set (Site 2)) ↔ x ∈ (↑K : Set (Site 2)) := by
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
  constructor
  · rintro (rfl | h); · exact absurd rfl hx
    · exact h
  · exact fun h => Or.inr h


theorem ats_bdEdge_insert_of_notMem {K : Finset (Site 2)} {c x y : Site 2}
    (hx : x ≠ c) (hy : y ≠ c) :
    bdEdge (↑(insert c K) : Set (Site 2)) s(x, y) ↔ bdEdge (↑K : Set (Site 2)) s(x, y) := by
  rw [bdEdge_mk, bdEdge_mk, ats_mem_insert_of_ne hx, ats_mem_insert_of_ne hy]


theorem ats_adj_insert_of_shared_avoid {K : Finset (Site 2)} {c f g u v : Site 2}
    (hshared : sharedPrimalEdge f g = s(u, v)) (hu : u ≠ c) (hv : v ≠ c) :
    (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Adj f g ↔
      (faceBoundaryGraph (↑K : Set (Site 2))).Adj f g := by
  rw [faceBoundaryGraph_adj, faceBoundaryGraph_adj, hshared,
    ats_bdEdge_insert_of_notMem hu hv]


end Walls
end StatMech
