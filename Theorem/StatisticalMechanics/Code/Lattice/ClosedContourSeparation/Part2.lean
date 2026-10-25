/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClosedContourSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanCoresUnify.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.ClusterDualContour
import Def.StatisticalMechanics.Code.Lattice.ClosedContourSeparation
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem ccs_clusterSeparatingSide {K : Set (Site 2)} (h : ccs_OrbitIsLoop K) :
    ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
      jcu_HasSeparatingSide Set.univ {z | z ∈ Vc.support} K Kᶜ := by
  obtain ⟨a, Vc, hin, hout⟩ := h
  refine ⟨a, Vc, ccs_closedLoop_separation Vc K Kᶜ ?_ ?_⟩
  · intro z hz; exact hin z hz
  · intro z hz; exact hout z hz


theorem ccs_cluster_forces_cross {K : Set (Site 2)} (h : ccs_OrbitIsLoop K)
    {x y : Site 2} (hx : x ∈ K) (hy : y ∉ K) (w : (hypercubicLattice 2).Walk x y) :
    ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
      (∀ z, z ∈ K → ¬ Even (jec_rayCount z Vc)) ∧
      (∀ z, z ∉ K → Even (jec_rayCount z Vc)) ∧
      ∃ z ∈ w.support, z ∈ Vc.support := by
  obtain ⟨a, Vc, hin, hout⟩ := h
  refine ⟨a, Vc, hin, hout, ?_⟩
  exact ccs_closedLoop_separatingSide_forces_cross Vc K Kᶜ hin hout hx hy w


theorem ccs_cluster_eq_leftRegion {K : Set (Site 2)} {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a)
    (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z Vc))
    (hout : ∀ z, z ∉ K → Even (jec_rayCount z Vc)) :
    K = jec_leftRegion Vc := by
  ext z
  rw [jec_mem_leftRegion]
  constructor
  · intro hz; exact hin z hz
  · intro hz; by_contra hzK; exact hz (hout z hzK)


theorem ccs_cluster_two_components {K : Set (Site 2)} (h : ccs_OrbitIsLoop K)
    {p q : Site 2} (hp : p ∈ K) (hq : q ∉ K)
    (hin : ∀ s t : Site 2, s ∈ K → t ∈ K → (latticeMinusBarrier K).Reachable s t)
    (hout : ∀ s t : Site 2, s ∉ K → t ∉ K → (latticeMinusBarrier K).Reachable s t) :
    Nat.card (latticeMinusBarrier K).ConnectedComponent = 2 ∧
      ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a), K = jec_leftRegion Vc := by
  obtain ⟨a, Vc, hLin, hLout⟩ := h
  refine ⟨jcs_two_components_of_sides K hp hq hin hout, a, Vc,
    ccs_cluster_eq_leftRegion Vc hLin hLout⟩


open StatMech.Percolation in


theorem ccs_pcSeparation_discharged
    (hloop : ∀ (ω : ConfigSpace (Sym2 (Site 2))), (cluster 2 ω (origin 2)).Finite →
        ccs_OrbitIsLoop (cluster 2 ω (origin 2))) :
    ∀ (ω : ConfigSpace (Sym2 (Site 2))), (cluster 2 ω (origin 2)).Finite →
      ∃ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a),
        jcu_HasSeparatingSide Set.univ {z | z ∈ Vc.support}
          (cluster 2 ω (origin 2)) (cluster 2 ω (origin 2))ᶜ :=
  fun ω hfin => ccs_clusterSeparatingSide (hloop ω hfin)

open StatMech.Percolation in


theorem ccs_pc_lt_one (hJordan : StatMech.Percolation.DiscreteJordanSeparation)
    (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        StatMech.Lattice.ExitDartsSameOrbit ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  StatMech.Percolation.pc_lt_one_of_jordan hJordan hsame

open StatMech.Percolation in


theorem ccs_pc_pos_and_lt_one (hJordan : StatMech.Percolation.DiscreteJordanSeparation)
    (hsame : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        StatMech.Lattice.ExitDartsSameOrbit ω hfin) :
    0 < StatMech.Percolation.pc 2 ∧ StatMech.Percolation.pc 2 < 1 :=
  StatMech.Percolation.pc_pos_and_lt_one_of_jordan hJordan hsame


end Lattice
end StatMech
