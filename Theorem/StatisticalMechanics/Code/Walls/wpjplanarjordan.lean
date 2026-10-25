/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpjplanarjordan.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InsideConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.FaceComponentBijection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem wpj_offSupport_edge_not_walkEdge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hu : u ∉ Vc.support) : s(u, v) ∉ Vc.edges :=
  fun he => hu (Vc.fst_mem_support_of_mem_edges he)


theorem wpj_face_adj_of_offSupport_wall (G : SimpleGraph (Site 2))
    {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hGV : G.edgeSet ⊆ {e | e ∈ Vc.edges})
    {f g u v : Site 2} (hfg : (hypercubicLattice 2).Adj f g)
    (hshared : sharedPrimalEdge f g = s(u, v)) (hu : u ∉ Vc.support) :
    (whb_faceRegion G).Adj f g := by
  rw [whb_faceRegion_adj]
  refine ⟨hfg, ?_⟩
  rw [hshared]
  intro hmem
  exact wpj_offSupport_edge_not_walkEdge Vc hu (hGV hmem)


theorem wpj_barrier_separates_inside_outside {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : x ∈ jec_leftRegion Vc) (hy : y ∉ jec_leftRegion Vc)
    (w : (hypercubicLattice 2).Walk x y) : ¬ Even (crossCount (jec_leftRegion Vc) w) :=
  crossCount_odd_of_separated (jec_leftRegion Vc) hx hy w


theorem wpj_latticeMinusBarrier_separates {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {x y : Site 2} (hx : x ∈ jec_leftRegion Vc) (hy : y ∉ jec_leftRegion Vc) :
    ¬ (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y :=
  not_reachable_latticeMinusBarrier (jec_leftRegion Vc) hx hy


end Lattice
end StatMech
