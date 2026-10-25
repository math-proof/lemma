/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonPerturbation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGenericPolygonReduction
import Structure.StatisticalMechanics.Code.FrontierA.KacWardPolygonPerturbation


namespace StatMech.FrontierA

open scoped Convex

open Set

noncomputable def KWRawSimplePolygonData.toFiniteSimplePolygon
    {n : ℕ} [NeZero n] {vertex : Fin n → ℂ}
    (h : KWRawSimplePolygonData vertex) : KWFiniteSimplePolygon n where
  vertex := vertex
  three_le := h.three_le
  vertex_injective := h.vertex_injective
  vertex_not_strictly_between := by
    intro i j hji hjs hs
    by_cases hprev : i = j + 1
    · have hzero := kwComplexCross_eq_zero_of_sbtw hs
      have hcross := h.cross_ne_zero j
      apply hcross
      unfold kwRawEdge
      rw [hprev] at hzero
      unfold kwComplexCross at hzero ⊢
      simp only [Complex.sub_re, Complex.sub_im] at hzero ⊢
      nlinarith
    · have hnon : KWEdgesNonincident i j := by
        exact ⟨hji.symm, hprev, hjs.symm⟩
      have hdis := h.nonincident_disjoint i j hnon
      apply Set.disjoint_left.mp hdis
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
        have hcrossCommon : kwComplexCross
            (vertex (j + 1 + 1) - vertex (j + 1))
            (vertex j - vertex (j + 1)) ≠ 0 := by
          have hcross := h.cross_ne_zero j
          intro hzero
          apply hcross
          unfold kwRawEdge
          unfold kwComplexCross at hzero ⊢
          simp only [Complex.sub_re, Complex.sub_im] at hzero ⊢
          linear_combination hzero
        have hd := kw_openSegments_disjoint_of_common_left_cross_ne
          hcrossCommon
        rw [Set.disjoint_left]
        intro z hzFirst hzSecond
        exact Set.disjoint_left.mp hd hzFirst ((sbtw_comm).mpr hzSecond)
      · subst j
        have hcrossCommon : kwComplexCross
            (vertex i - vertex (i + 1))
            (vertex (i + 1 + 1) - vertex (i + 1)) ≠ 0 := by
          have hcross := h.cross_ne_zero i
          intro hzero
          apply hcross
          unfold kwRawEdge
          unfold kwComplexCross at hzero ⊢
          simp only [Complex.sub_re, Complex.sub_im] at hzero ⊢
          linear_combination -hzero
        have hd := kw_openSegments_disjoint_of_common_left_cross_ne
          hcrossCommon
        rw [Set.disjoint_left]
        intro z hzFirst hzSecond
        exact Set.disjoint_left.mp hd ((sbtw_comm).mpr hzFirst) hzSecond


end StatMech.FrontierA
