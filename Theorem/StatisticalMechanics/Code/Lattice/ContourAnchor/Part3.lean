/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.ContourAnchor.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Percolation (anchorFinset origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem axisSite_exit_succ_not_mem (hfin : (cluster 2 ω (origin 2)).Finite) :
    axisSite (exitIndex (ω := ω) hfin + 1) ∉ cluster 2 ω (origin 2) := by
  classical
  exact Nat.find_spec (exitPred_exists (ω := ω) hfin)


theorem axisSite_lt_exit_mem (hfin : (cluster 2 ω (origin 2)).Finite) {m : ℕ}
    (hm : m < exitIndex (ω := ω) hfin) :
    axisSite (m + 1) ∈ cluster 2 ω (origin 2) := by
  classical
  have hnot : ¬ exitPred ω m := Nat.find_min (exitPred_exists (ω := ω) hfin) hm
  exact not_not.mp hnot


theorem axisSite_exit_mem (hfin : (cluster 2 ω (origin 2)).Finite) :
    axisSite (exitIndex (ω := ω) hfin) ∈ cluster 2 ω (origin 2) := by
  classical
  
  have hin : ∀ k, k ≤ exitIndex (ω := ω) hfin → axisSite k ∈ cluster 2 ω (origin 2) := by
    intro k hk
    induction k with
    | zero => exact axisSite_zero_mem_cluster (ω := ω)
    | succ m _ =>
      exact axisSite_lt_exit_mem (ω := ω) hfin (Nat.lt_of_succ_le hk)
  exact hin _ le_rfl


theorem axisSite_exit_adj (hfin : (cluster 2 ω (origin 2)).Finite) :
    (hypercubicLattice 2).Adj (axisSite (exitIndex (ω := ω) hfin))
      (axisSite (exitIndex (ω := ω) hfin + 1)) := by
  set j := exitIndex (ω := ω) hfin
  have hsucc : (axisSite (j + 1) : Site 2) = ![(j : ℤ) + 1, 0] := by
    funext i; fin_cases i <;> simp [axisSite]
  rw [show (axisSite j : Site 2) = ![(j : ℤ), 0] from rfl, hsucc]
  exact latAdj_right (j : ℤ) 0


theorem axisExitEdge_mem_edgeBoundary (hfin : (cluster 2 ω (origin 2)).Finite) :
    (axisSite (exitIndex (ω := ω) hfin), axisSite (exitIndex (ω := ω) hfin + 1))
      ∈ edgeBoundary 2 (cluster 2 ω (origin 2)) := by
  rw [mem_edgeBoundary]
  refine ⟨axisSite_exit_adj (ω := ω) hfin, ?_⟩
  rw [iff_true_intro (axisSite_exit_mem (ω := ω) hfin)]
  exact iff_of_true trivial (axisSite_exit_succ_not_mem (ω := ω) hfin)


theorem axisExitEdge_isClosed (hfin : (cluster 2 ω (origin 2)).Finite) :
    ω s(axisSite (exitIndex (ω := ω) hfin), axisSite (exitIndex (ω := ω) hfin + 1)) = false :=
  cluster_edgeBoundary_isClosed (origin 2) (axisExitEdge_mem_edgeBoundary (ω := ω) hfin)


end Lattice
end StatMech
