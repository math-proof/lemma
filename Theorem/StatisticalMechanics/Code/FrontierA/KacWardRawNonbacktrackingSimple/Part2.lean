/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRawNonbacktrackingSimple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveVertexConnector.Part2
import Structure.StatisticalMechanics.Code.FrontierA.KacWardRawNonbacktrackingSimple


namespace StatMech.FrontierA

open scoped Convex

open Set

theorem KWRawNonbacktrackingSimpleData.vertex_injective
    {n : ℕ} [NeZero n] {vertex : Fin n → ℂ}
    (h : KWRawNonbacktrackingSimpleData vertex) :
    Function.Injective vertex := by
  intro i j hij
  by_contra hne
  by_cases hprev : i = j + 1
  · have hedge : kwRawEdge vertex j = 0 := by
      unfold kwRawEdge
      rw [← hprev, hij]
      exact sub_self _
    exact h.edge_ne_zero j hedge
  by_cases hnext : i + 1 = j
  · have hedge : kwRawEdge vertex i = 0 := by
      unfold kwRawEdge
      rw [hnext, hij]
      exact sub_self _
    exact h.edge_ne_zero i hedge
  have hnon : KWEdgesNonincident i j := ⟨hne, hprev, hnext⟩
  apply Set.disjoint_left.mp (h.nonincident_disjoint i j hnon)
  · exact left_mem_segment ℝ _ _
  · rw [kwRawClosedEdge, ← hij]
    exact left_mem_segment ℝ _ _


end StatMech.FrontierA
