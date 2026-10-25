/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jbwbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
import Def.StatisticalMechanics.Code.Walls.jbwbridge.Part3
open SimpleGraph Set


namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising

attribute [local instance] Classical.propDecidable


theorem jbw_hardGap_iff_windingBody {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    (jbw_hard_gap Vc ∧
      ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
        bdEdge (jec_leftRegion Vc) s(u, v) → s(u, v) ∈ Vc.edges.toFinset)
    ↔ (∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
        (s(u, v) ∈ Vc.edges.toFinset ↔ bdEdge (jec_leftRegion Vc) s(u, v))) := by
  constructor
  · rintro ⟨hf, hb⟩ u v hadj
    exact ⟨fun h => hf hadj h, fun h => hb hadj h⟩
  · intro h
    exact ⟨fun hadj he => (h hadj).mp he, fun hadj hb => (h hadj).mpr hb⟩


theorem jbw_hard_gap_of_windingMatch (hmatch : kwc_PrimalWalkLeftRegionMatch)
    {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) : jbw_hard_gap Vc := by
  intro u v hadj he
  exact (hmatch Vc hadj).mp he


theorem jbw_jed_insufficient :
    
    (¬ Even (jce_degree (jbw_bdEdgeSet jbw_singleton) ![(1 : ℤ), 0])) ∧
    
    (∀ (H : SimpleGraph (Site 2)), H.edgeSet.Finite → ∀ (p q f0 g0 : Site 2),
        (hypercubicLattice 2).Adj p q → s(p, q) ∉ H.edgeSet →
        (hypercubicLattice 2).Adj f0 g0 → sharedPrimalEdge f0 g0 = s(p, q) →
        ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 → H.Reachable p q) ∧
    
    (kwc_PrimalWalkLeftRegionMatch →
      ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), jbw_hard_gap Vc) :=
  ⟨jbw_vertexCut_not_even, jbw_jed_reachability, fun h _ Vc => jbw_hard_gap_of_windingMatch h Vc⟩

end Walls
end StatMech
