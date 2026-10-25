/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc55route
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Def.StatisticalMechanics.Code.Walls.bc56menger.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc56_boxClusterAttachment_of_reachesNbr {n : ℕ}
    (h : bc56_BoxClusterReachesNbr d n) : bma_BoxClusterAttachment d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨h1, h2, h3⟩ := h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact ⟨bc56_clusterAttachment_of_reachesNbr ω x₁ h1,
    bc56_clusterAttachment_of_reachesNbr ω x₂ h2,
    bc56_clusterAttachment_of_reachesNbr ω x₃ h3⟩


theorem bc56_boxMengerAttachment_of_reachesNbr {n : ℕ}
    (h : bc56_BoxClusterReachesNbr d n) : bmm_BoxMengerAttachment d n :=
  bma_boxMengerAttachment (bc56_boxClusterAttachment_of_reachesNbr h)


theorem bc56_burton_keane_bernoulli_of_reachesNbr (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p) (h : ∀ n : ℕ, bc56_BoxClusterReachesNbr d n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc55_burton_keane_bernoulli_of_boxMenger hd p hp1 hp0
    (fun n => bc56_boxMengerAttachment_of_reachesNbr (h n))


theorem bc56_reachesNbr_of_neighbour (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hadj : (hypercubicLattice d).Adj 0 x)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
    bc56_ClusterReachesNbr ω x :=
  ⟨x, hadj, self_mem_cluster ω x, connected_rfl, hinf⟩


theorem bc56_threeRayConfig_reachesNbr_witness :
    bc56_ClusterReachesNbr CtcWitness.threeRayConfig (CtcWitness.px 1) ∧
    bc56_ClusterReachesNbr CtcWitness.threeRayConfig (CtcWitness.px (-1)) ∧
    bc56_ClusterReachesNbr CtcWitness.threeRayConfig (CtcWitness.py 1) := by
  have h0 : (CtcWitness.px 0 : Site 2) = 0 := by
    funext i; fin_cases i <;> simp [CtcWitness.px]
  have hadjpx1 : (hypercubicLattice 2).Adj 0 (CtcWitness.px 1) := by
    have := CtcWitness.px_adj 0
    rw [show (0 : ℤ) + 1 = 1 by ring] at this
    rwa [h0] at this
  have hadjpxm1 : (hypercubicLattice 2).Adj 0 (CtcWitness.px (-1)) := by
    have := CtcWitness.px_adj (-1)
    rw [show (-1 : ℤ) + 1 = 0 by ring, h0] at this
    exact this.symm
  have hadjpy1 : (hypercubicLattice 2).Adj 0 (CtcWitness.py 1) := by
    have := CtcWitness.py_adj 0
    rw [show (0 : ℤ) + 1 = 1 by ring, ← CtcWitness.px_zero_eq_py_zero, h0] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨CtcWitness.px 1, hadjpx1, self_mem_cluster _ _, connected_rfl, ?_⟩
    rw [← h0]; exact CtcWitness.cut_px_pos_infinite
  · refine ⟨CtcWitness.px (-1), hadjpxm1, self_mem_cluster _ _, connected_rfl, ?_⟩
    rw [← h0]; exact CtcWitness.cut_px_neg_infinite
  · refine ⟨CtcWitness.py 1, hadjpy1, self_mem_cluster _ _, connected_rfl, ?_⟩
    rw [← h0]; exact CtcWitness.cut_py_pos_infinite


theorem bc56_runsAlongAxis_forces_nbr_in_cluster (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (j : Fin d) (h : crr_ClusterRunsAlongAxis ω x j) :
    hrHD_rayPt j 1 ∈ cluster d ω x := by
  obtain ⟨L, _, hxe1, _, _⟩ := h
  rw [mem_cluster]; exact hxe1


end StatMech.Walls
