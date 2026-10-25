/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwceventtocut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.DualWalkBoundsClose.Part3
import Def.StatisticalMechanics.Code.Walls.kwceventtocut.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising


theorem kwc_primalWalkBoundsRegion_of_leftRegionMatch
    (hmatch : kwc_PrimalWalkLeftRegionMatch) :
    PrimalWalkBoundsRegion := by
  intro a Vc
  exact ⟨jec_leftRegion Vc, fun h => hmatch Vc h⟩


theorem kwc_leftRegion_bdEdge_incident {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support :=
  jec_leftRegion_bdEdge_support Vc hadj hbd


theorem kwc_primalWalkBoundsRegion_nil_case {a : Site 2} :
    ∃ S : Set (Site 2), ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a).edges.toFinset
        ↔ bdEdge S s(u, v)) := by
  refine ⟨(∅ : Set (Site 2)), ?_⟩
  intro u v _
  simp only [SimpleGraph.Walk.edges_nil, List.toFinset_nil, Finset.notMem_empty, bdEdge_mk,
    Set.mem_empty_iff_false, not_false_iff]
  tauto

end Walls
end StatMech
