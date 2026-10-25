/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
import Def.StatisticalMechanics.Code.Universality.DualCutToPath.Part3
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


theorem dcp_barrierWalk_support_rot (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (c : (dcw_dualBarrierGraph ω n).Walk p q) (hp : p ∈ rect (-n) 0 0 n) :
    ∀ u ∈ c.support, u ∈ rect (-n) 0 0 n := by
  induction c with
  | nil => intro u hu; rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu; rwa [hu]
  | @cons a b d hab p ih =>
    intro u hu
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact hp
    · exact ih (dcp_dualBarrierGraph_support_rot ω n hab.symm) u hu


theorem dcp_rotatedDualVerticalCrossing_of_cutConnectsRot
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hcut : dcp_DualCutConnectsRot ω n) :
    DualVerticalCrossing ω (-n) 0 0 n := by
  obtain ⟨p₀, hp₀, q₀, hq₀, hreach⟩ := hcut
  rw [dualVerticalCrossing_iff]
  
  obtain ⟨c⟩ := hreach
  set c' : (openSubgraph 2 (dualConfig ω)).Walk p₀ q₀ := dcw_dualBarrier_walk_open ω n c
    with hc'
  
  have hsupp' : c'.support = c.support := by
    rw [hc', dcw_dualBarrier_walk_open, SimpleGraph.Walk.support_mapLe_eq_support]
  have hsuppbox : ∀ u ∈ c'.support, u ∈ rect (-n) 0 0 n := by
    intro u hu
    rw [hsupp'] at hu
    exact dcp_barrierWalk_support_rot ω n c (bottomSide_subset hp₀) u hu
  refine ⟨⟨p₀, hp₀⟩, ⟨q₀, hq₀⟩, ?_⟩
  exact walk_induce_reachable (openSubgraph 2 (dualConfig ω)) (rect (-n) 0 0 n) c'
    hsuppbox (bottomSide_subset hp₀) (topSide_subset hq₀)


theorem dcp_rotatedCut_nonempty_edge (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ p q : Site 2, (dcw_dualBarrierGraph ω n).Adj p q ∧
      p ∈ rect (-n) 0 0 n ∧ q ∈ rect (-n) 0 0 n := by
  obtain ⟨p, q, hpq⟩ := dcw_dualBarrierGraph_nonempty_edge ω n hn hnoH
  exact ⟨p, q, hpq, dcp_dualBarrierGraph_support_rot ω n hpq,
    dcp_dualBarrierGraph_support_rot ω n hpq.symm⟩

end Universality
end StatMech
