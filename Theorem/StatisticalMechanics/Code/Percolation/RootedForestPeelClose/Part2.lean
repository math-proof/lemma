/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BKHallSDRClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ForestAcyclicityClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.FacPairwiseClose
import Theorem.StatisticalMechanics.Code.Percolation.BKArmSelectorClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.RootedTreeSelectorClose
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestColouringClose2.Part3
import Def.StatisticalMechanics.Code.Percolation.RootedForestPeelClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem rfp_consistency_beyond :
    Connected 1 (removeSite rfp_p0 rfp_ωpath) rfp_p2 rfp_p1 := by
  refine SimpleGraph.Adj.reachable (G := openSubgraph 1 (removeSite rfp_p0 rfp_ωpath)) ?_
  refine ⟨?_, ?_⟩
  · rw [hypercubicLattice_adj]; simp [rfp_p1, rfp_p2]
  · have hp0 : rfp_p0 ∉ s(rfp_p2, rfp_p1) := by
      simp only [Sym2.mem_iff, not_or]
      refine ⟨?_, ?_⟩
      · intro h; have := congrFun h ⟨0, by norm_num⟩; simp [rfp_p0, rfp_p2] at this
      · intro h; have := congrFun h ⟨0, by norm_num⟩; simp [rfp_p0, rfp_p1] at this
    rw [removeSite_apply_of_notMem hp0]
    change decide (s(rfp_p2, rfp_p1) = s(rfp_p0, rfp_p1) ∨ s(rfp_p2, rfp_p1) = s(rfp_p1, rfp_p2))
        = true
    simp only [decide_eq_true_eq]
    right; rw [Sym2.eq_swap]


theorem rfp_path_noEdge_after_p1 (a b : Site 1) :
    ¬ (openSubgraph 1 (removeSite rfp_p1 rfp_ωpath)).Adj a b := by
  rintro ⟨_hadj, hopen⟩
  by_cases hp1 : rfp_p1 ∈ s(a, b)
  · rw [removeSite_apply_of_mem hp1] at hopen; exact Bool.false_ne_true hopen
  · rw [removeSite_apply_of_notMem hp1] at hopen
    have h2 : s(a, b) = s(rfp_p0, rfp_p1) ∨ s(a, b) = s(rfp_p1, rfp_p2) := by
      simpa only [rfp_ωpath, decide_eq_true_eq] using hopen
    rcases h2 with h | h
    · exact hp1 (h ▸ Sym2.mem_mk_right rfp_p0 rfp_p1)
    · exact hp1 (h ▸ Sym2.mem_mk_left rfp_p1 rfp_p2)


theorem rfp_path_conn_eq_after_p1 {a b : Site 1}
    (h : Connected 1 (removeSite rfp_p1 rfp_ωpath) a b) : a = b := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (rfp_path_noEdge_after_p1 _ _)


theorem rfp_consistency_crossed :
    ¬ Connected 1 (removeSite rfp_p1 rfp_ωpath) rfp_p2 rfp_p0 := by
  intro h
  have heq := rfp_path_conn_eq_after_p1 h
  have := congrFun heq ⟨0, by norm_num⟩
  simp [rfp_p0, rfp_p2] at this


theorem rfp_armGeometry_consistent :
    ∃ (ω : ConfigSpace (Sym2 (Site 1))) (x₀ z w : Site 1),
      Connected 1 (removeSite x₀ ω) w z ∧ ¬ Connected 1 (removeSite z ω) w x₀ :=
  ⟨rfp_ωpath, rfp_p0, rfp_p1, rfp_p2, rfp_consistency_beyond, rfp_consistency_crossed⟩


end Percolation
end StatMech
