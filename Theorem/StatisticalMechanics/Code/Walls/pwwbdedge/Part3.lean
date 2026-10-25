/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pwwbdedge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchClose
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
import Def.StatisticalMechanics.Code.Walls.pwwbdedge.Part3
open Set SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem pww_leftRegionMatch_of_cycle_forward {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcrux : pww_ForwardCrux Vc)
    (hback : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      bdEdge (jec_leftRegion Vc) s(u, v) → s(u, v) ∈ Vc.edges.toFinset)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v) :
    s(u, v) ∈ Vc.edges.toFinset ↔ bdEdge (jec_leftRegion Vc) s(u, v) :=
  ⟨fun h => hcrux hadj h, fun h => hback hadj h⟩


theorem pww_leftRegionMatch_nil {a : Site 2} {u v : Site 2}
    (_hadj : (hypercubicLattice 2).Adj u v) :
    (s(u, v) ∈ (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a).edges.toFinset
      ↔ bdEdge (jec_leftRegion (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a)) s(u, v)) := by
  have hleft : jec_leftRegion (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a)
      = (∅ : Set (Site 2)) := by
    ext z
    simp only [jec_mem_leftRegion, jec_rayCount_nil, Set.mem_empty_iff_false, iff_false, not_not]
    exact ⟨0, rfl⟩
  rw [hleft]
  simp

end Walls
end StatMech
