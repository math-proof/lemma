/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Def.StatisticalMechanics.Code.Lattice.LeftFace.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem leftAxisSite_exit_succ_not_mem (hfin : (cluster 2 ω (origin 2)).Finite) :
    leftAxisSite (leftExitIndex (ω := ω) hfin + 1) ∉ cluster 2 ω (origin 2) := by
  classical
  exact Nat.find_spec (leftExitPred_exists (ω := ω) hfin)


theorem leftAxisSite_lt_exit_mem (hfin : (cluster 2 ω (origin 2)).Finite) {m : ℕ}
    (hm : m < leftExitIndex (ω := ω) hfin) :
    leftAxisSite (m + 1) ∈ cluster 2 ω (origin 2) := by
  classical
  have hnot : ¬ leftExitPred ω m := Nat.find_min (leftExitPred_exists (ω := ω) hfin) hm
  exact not_not.mp hnot


theorem leftAxisSite_exit_mem (hfin : (cluster 2 ω (origin 2)).Finite) :
    leftAxisSite (leftExitIndex (ω := ω) hfin) ∈ cluster 2 ω (origin 2) := by
  classical
  have hin : ∀ k, k ≤ leftExitIndex (ω := ω) hfin →
      leftAxisSite k ∈ cluster 2 ω (origin 2) := by
    intro k hk
    induction k with
    | zero => exact leftAxisSite_zero_mem_cluster (ω := ω)
    | succ m _ =>
      exact leftAxisSite_lt_exit_mem (ω := ω) hfin (Nat.lt_of_succ_le hk)
  exact hin _ le_rfl


theorem leftAxisSite_eq (k : ℕ) : (leftAxisSite k : Site 2) = ![-(k : ℤ), 0] := rfl


theorem leftAxisSite_succ_eq (k : ℕ) :
    (leftAxisSite (k + 1) : Site 2) = ![-(k : ℤ) - 1, 0] := by
  funext i; fin_cases i
  · simp only [leftAxisSite, Nat.cast_add, Nat.cast_one]
    ring_nf
  · simp [leftAxisSite]


theorem leftAxisSite_exit_adj (hfin : (cluster 2 ω (origin 2)).Finite) :
    (hypercubicLattice 2).Adj (leftAxisSite (leftExitIndex (ω := ω) hfin))
      (leftAxisSite (leftExitIndex (ω := ω) hfin + 1)) := by
  set k := leftExitIndex (ω := ω) hfin
  rw [leftAxisSite_eq k, leftAxisSite_succ_eq k]
  simp [hypercubicLattice_adj, Fin.sum_univ_two]


theorem leftExitEdge_mem_edgeBoundary (hfin : (cluster 2 ω (origin 2)).Finite) :
    (leftAxisSite (leftExitIndex (ω := ω) hfin),
        leftAxisSite (leftExitIndex (ω := ω) hfin + 1))
      ∈ edgeBoundary 2 (cluster 2 ω (origin 2)) := by
  rw [mem_edgeBoundary]
  refine ⟨leftAxisSite_exit_adj (ω := ω) hfin, ?_⟩
  rw [iff_true_intro (leftAxisSite_exit_mem (ω := ω) hfin)]
  exact iff_of_true trivial (leftAxisSite_exit_succ_not_mem (ω := ω) hfin)


theorem leftExitEdge_isClosed (hfin : (cluster 2 ω (origin 2)).Finite) :
    ω s(leftAxisSite (leftExitIndex (ω := ω) hfin),
        leftAxisSite (leftExitIndex (ω := ω) hfin + 1)) = false :=
  cluster_edgeBoundary_isClosed (origin 2) (leftExitEdge_mem_edgeBoundary (ω := ω) hfin)


end Lattice
end StatMech
