/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanSeparationClose
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem jsc_separation_of_JordanSeparates {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : jsc_JordanSeparates Vc) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 ∧
      (∃ q : Site 2, q ∉ jec_leftRegion Vc) ∧
      (∀ x y : Site 2, ¬ Even (jec_rayCount x Vc) → Even (jec_rayCount y Vc) →
        ¬ (latticeMinusBarrier (jec_leftRegion Vc)).Reachable x y) := by
  obtain ⟨⟨p, hp⟩, hin, hout⟩ := h
  obtain ⟨q, hq, _⟩ := jsc_exists_outside Vc
  exact ⟨jsc_two_components_of_connected Vc hp hin hout, ⟨q, hq⟩,
    fun x y hx hy => jsc_inside_not_reachable_outside Vc hx hy⟩


theorem jsc_cycle_faceCount_eq_two {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) :
    faceCount c.toSubgraph.coe = 2 :=
  jcs_cycle_faceCount_eq_two c hc


theorem jsc_cycle_separation {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) (hsep : jsc_JordanSeparates Vc) :
    faceCount Vc.toSubgraph.coe = 2 ∧
      Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
  obtain ⟨⟨p, hp⟩, hin, hout⟩ := hsep
  exact ⟨jsc_cycle_faceCount_eq_two Vc hcyc, jsc_two_components_of_connected Vc hp hin hout⟩


theorem jsc_cluster_inside_connected (o : Site 2) {x y : Site 2}
    (hx : x ∈ cluster 2 ω o) (hy : y ∈ cluster 2 ω o) :
    (latticeMinusBarrier (cluster 2 ω o)).Reachable x y :=
  cluster_reachable_in_barrier o hx hy


theorem jsc_separation_of_loopBridge (o : Site 2) (hfin : (cluster 2 ω o).Finite)
    (hloop : ccs_OrbitIsLoop (cluster 2 ω o))
    (hout : ∀ s t : Site 2, s ∉ cluster 2 ω o → t ∉ cluster 2 ω o →
        (latticeMinusBarrier (cluster 2 ω o)).Reachable s t) :
    Nat.card (latticeMinusBarrier (cluster 2 ω o)).ConnectedComponent = 2 ∧
      ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
        cluster 2 ω o = jec_leftRegion Vc := by
  obtain ⟨R, hR⟩ := finite_subset_box (cluster 2 ω o) hfin
  
  have hpin : o ∈ cluster 2 ω o := self_mem_cluster ω o
  
  have hbe : beacon 2 R ∈ exterior 2 R := beacon_mem_exterior R (by norm_num)
  have hqout : beacon 2 R ∉ cluster 2 ω o := (exterior_subset_compl (cluster 2 ω o) R hR) hbe
  refine ccs_cluster_two_components (K := cluster 2 ω o) hloop hpin hqout ?_ hout
  
  intro s t hs ht; exact cluster_reachable_in_barrier o hs ht


end Lattice
end StatMech
