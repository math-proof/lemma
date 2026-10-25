/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.atsattachsurgery.Part4
import Theorem.StatisticalMechanics.Code.Walls.arrreroute.Part5
import Def.StatisticalMechanics.Code.Walls.cycboundary
open Finset Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem cyc_connected {K : Set (Site 2)} (h : cyc_BoundaryCycle K) : fbc_BoundaryReachable K :=
  h.1


theorem cyc_degreeTwo {K : Set (Site 2)} (h : cyc_BoundaryCycle K)
    {f : Site 2} (hf : f ∈ (faceBoundaryGraph K).support) :
    (faceBoundaryGraph K).degree f = 2 :=
  h.2 f hf


theorem cyc_boundaryCycle_imp_reachable {K : Set (Site 2)} (h : cyc_BoundaryCycle K) :
    fbc_BoundaryReachable K :=
  h.1


theorem cyc_degree_pos_of_support {K : Set (Site 2)} {f : Site 2}
    (hf : f ∈ (faceBoundaryGraph K).support) :
    0 < (faceBoundaryGraph K).degree f := by
  classical
  obtain ⟨g, hg⟩ := hf
  rw [SimpleGraph.degree, Finset.card_pos]
  exact ⟨g, by rw [SimpleGraph.mem_neighborFinset]; exact hg⟩


theorem cyc_degree_ge_two_of_support {K : Set (Site 2)} {f : Site 2}
    (hf : f ∈ (faceBoundaryGraph K).support) :
    2 ≤ (faceBoundaryGraph K).degree f := by
  have heven := degree_faceBoundaryGraph_even K f
  have hpos := cyc_degree_pos_of_support hf
  rcases heven with ⟨k, hk⟩
  omega


theorem cyc_degree_two_iff_le_two {K : Set (Site 2)} {f : Site 2}
    (hf : f ∈ (faceBoundaryGraph K).support) :
    (faceBoundaryGraph K).degree f = 2 ↔ (faceBoundaryGraph K).degree f ≤ 2 := by
  have hge := cyc_degree_ge_two_of_support hf
  omega


end Walls
end StatMech
