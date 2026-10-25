/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForwardSubdivision
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue.Part2
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisSubdivision


namespace StatMech.FrontierA

open Set

open scoped BigOperators

open StatMech.Onsager.BaseCase


theorem KWRawNonbacktrackingSimpleData.halfOpenEdge_subset_closedEdge
    {n : ℕ} [NeZero n] {vertex : Fin n → ℂ}
    (h : KWRawNonbacktrackingSimpleData vertex) (i : Fin n) :
    kwRawHalfOpenEdge vertex i ⊆ kwRawClosedEdge vertex i := by
  rintro z (rfl | hz)
  · exact left_mem_segment ℝ _ _
  · exact mem_segment_iff_wbtw.mpr hz.1

theorem KWRawNonbacktrackingSimpleData.halfOpenEdge_disjoint_succ
    {n : ℕ} [NeZero n] {vertex : Fin n → ℂ}
    (h : KWRawNonbacktrackingSimpleData vertex) (i : Fin n) :
    Disjoint (kwRawHalfOpenEdge vertex i)
      (kwRawHalfOpenEdge vertex (i + 1)) := by
  have hone : (1 : Fin n) + 1 = 2 := by
    apply Fin.ext
    change (1 % n + 1 % n) % n = 2 % n
    rw [← Nat.add_mod]
  have hi2 : i + 1 + 1 = i + 2 := by
    rw [add_assoc, hone]
  rw [Set.disjoint_left]
  rintro z (hzi | hzi) (hzj | hzj)
  · apply h.edge_ne_zero i
    unfold kwRawEdge
    rw [← hzi, hzj]
    exact sub_self _
  · subst z
    exact h.previous_not_between i (by simpa only [hi2] using hzj)
  · subst z
    exact hzi.ne_right rfl
  · exact Set.disjoint_left.mp (h.adjacent_disjoint i) hzi
      (by simpa only [hi2] using hzj)


theorem KWRawNonbacktrackingSimpleData.halfOpenEdge_disjoint
    {n : ℕ} [NeZero n] {vertex : Fin n → ℂ}
    (h : KWRawNonbacktrackingSimpleData vertex)
    {i j : Fin n} (hij : i ≠ j) :
    Disjoint (kwRawHalfOpenEdge vertex i)
      (kwRawHalfOpenEdge vertex j) := by
  by_cases hnon : KWEdgesNonincident i j
  · exact (h.nonincident_disjoint i j hnon).mono
      (h.halfOpenEdge_subset_closedEdge i)
      (h.halfOpenEdge_subset_closedEdge j)
  · have hadj : i = j + 1 ∨ i + 1 = j := by
      by_contra hnot
      apply hnon
      exact ⟨hij, (not_or.mp hnot).1, (not_or.mp hnot).2⟩
    rcases hadj with hprev | hnext
    · subst i
      exact (h.halfOpenEdge_disjoint_succ j).symm
    · subst j
      exact h.halfOpenEdge_disjoint_succ i


end StatMech.FrontierA
