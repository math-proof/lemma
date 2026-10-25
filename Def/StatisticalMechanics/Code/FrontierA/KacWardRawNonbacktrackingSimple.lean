/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRawNonbacktrackingSimple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveVertexConnector.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRawNonbacktrackingSimple.Part2


namespace StatMech.FrontierA

open scoped Convex

open Set

noncomputable def KWRawNonbacktrackingSimpleData.toFiniteSimplePolygon
    {n : ℕ} [NeZero n] {vertex : Fin n → ℂ}
    (h : KWRawNonbacktrackingSimpleData vertex) :
    KWFiniteSimplePolygon n where
  vertex := vertex
  three_le := h.three_le
  vertex_injective := h.vertex_injective
  vertex_not_strictly_between := by
    intro i j hji hjs hs
    by_cases hprev : i = j + 1
    · subst i
      exact h.previous_not_between j
        (by simpa only [fin_add_one_plus_one, fin_add_one_add_one] using hs)
    · have hnon : KWEdgesNonincident i j :=
        ⟨hji.symm, hprev, hjs.symm⟩
      apply Set.disjoint_left.mp (h.nonincident_disjoint i j hnon)
      · exact mem_segment_iff_wbtw.mpr hs.1
      · exact left_mem_segment ℝ _ _
  edgeInteriors_disjoint := by
    intro i j hij
    by_cases hnon : KWEdgesNonincident i j
    · exact (h.nonincident_disjoint i j hnon).mono
        (fun _ hz ↦ mem_segment_iff_wbtw.mpr hz.1)
        (fun _ hz ↦ mem_segment_iff_wbtw.mpr hz.1)
    · have hadj : i = j + 1 ∨ i + 1 = j := by
        by_contra hnot
        apply hnon
        refine ⟨hij, ?_, ?_⟩
        · exact (not_or.mp hnot).1
        · exact (not_or.mp hnot).2
      rcases hadj with hprev | hnext
      · subst i
        simpa only [fin_add_one_add_one] using (h.adjacent_disjoint j).symm
      · subst j
        simpa only [fin_add_one_add_one] using h.adjacent_disjoint i

end StatMech.FrontierA
