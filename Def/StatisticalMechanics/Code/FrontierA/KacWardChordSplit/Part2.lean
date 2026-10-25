/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardVisibleDiagonal
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordSplit


namespace StatMech.FrontierA

noncomputable def KWFiniteSimplePolygon.prefixOfCleanChord
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 2 ≤ j.val)
    (hclean : polygon.ChordIsClean 0 j) :
    KWFiniteSimplePolygon (j.val + 1) where
  vertex := fun k ↦ polygon.vertex (kwChordPrefixIndex j k)
  three_le := by omega
  vertex_injective := polygon.vertex_injective.comp
    (kwChordPrefixIndex_injective j)
  vertex_not_strictly_between := by
    intro q k hkq hkNext
    revert k
    refine Fin.lastCases ?_ (fun p ↦ ?_) q
    · intro k hkq hkNext
      have hk0 : kwChordPrefixIndex j k ≠ 0 := by
        intro h
        apply hkNext
        apply kwChordPrefixIndex_injective j
        simpa only [kwChordPrefixIndex_last_add_one] using h
      have hkj : kwChordPrefixIndex j k ≠ j := by
        intro h
        apply hkq
        apply kwChordPrefixIndex_injective j
        simpa only [kwChordPrefixIndex_last] using h
      simp only [kwChordPrefixIndex_last,
        kwChordPrefixIndex_last_add_one]
      change ¬Sbtw ℝ (polygon.vertex j)
        (polygon.vertex (kwChordPrefixIndex j k)) (polygon.vertex 0)
      rw [sbtw_comm]
      exact hclean.1 (kwChordPrefixIndex j k) hk0 hkj
    · intro k hkq hkNext
      have hkStart : kwChordPrefixIndex j k ≠
          kwChordPrefixIndex j p.castSucc :=
        (kwChordPrefixIndex_injective j).ne hkq
      have hkEnd : kwChordPrefixIndex j k ≠
          kwChordPrefixIndex j p.castSucc + 1 := by
        rw [← kwChordPrefixIndex_castSucc_add_one j p]
        exact (kwChordPrefixIndex_injective j).ne hkNext
      change ¬Sbtw ℝ
        (polygon.vertex (kwChordPrefixIndex j p.castSucc))
        (polygon.vertex (kwChordPrefixIndex j k))
        (polygon.vertex (kwChordPrefixIndex j (p.castSucc + 1)))
      rw [kwChordPrefixIndex_castSucc_add_one]
      exact polygon.vertex_not_strictly_between
        (kwChordPrefixIndex j p.castSucc) (kwChordPrefixIndex j k)
        hkStart hkEnd
  edgeInteriors_disjoint := by
    intro q k hqk
    revert k
    refine Fin.lastCases ?_ (fun p ↦ ?_) q
    · intro k hqk
      refine Fin.lastCases (fun h ↦ (h rfl).elim) (fun s h ↦ ?_) k hqk
      simp only [kwChordPrefixIndex_last,
        kwChordPrefixIndex_last_add_one]
      change Disjoint
        {z : ℂ | Sbtw ℝ (polygon.vertex j) z (polygon.vertex 0)}
        {z : ℂ | Sbtw ℝ
          (polygon.vertex (kwChordPrefixIndex j s.castSucc)) z
          (polygon.vertex (kwChordPrefixIndex j (s.castSucc + 1)))}
      rw [kwChordPrefixIndex_castSucc_add_one]
      rw [Set.disjoint_left]
      intro z hzChord hzEdge
      exact Set.disjoint_left.mp (hclean.2
        (kwChordPrefixIndex j s.castSucc))
        ((sbtw_comm).mpr hzChord) hzEdge
    · intro k hqk
      refine Fin.lastCases (fun h ↦ ?_) (fun s h ↦ ?_) k hqk
      · simp only [kwChordPrefixIndex_last,
          kwChordPrefixIndex_last_add_one]
        change Disjoint
          {z : ℂ | Sbtw ℝ
            (polygon.vertex (kwChordPrefixIndex j p.castSucc)) z
            (polygon.vertex
              (kwChordPrefixIndex j (p.castSucc + 1)))}
          {z : ℂ | Sbtw ℝ (polygon.vertex j) z (polygon.vertex 0)}
        rw [kwChordPrefixIndex_castSucc_add_one]
        rw [Set.disjoint_left]
        intro z hzEdge hzChord
        exact Set.disjoint_left.mp (hclean.2
          (kwChordPrefixIndex j p.castSucc))
          ((sbtw_comm).mpr hzChord) hzEdge
      · have hpNe : kwChordPrefixIndex j p.castSucc ≠
            kwChordPrefixIndex j s.castSucc :=
          (kwChordPrefixIndex_injective j).ne h
        change Disjoint
          {z : ℂ | Sbtw ℝ
            (polygon.vertex (kwChordPrefixIndex j p.castSucc)) z
            (polygon.vertex (kwChordPrefixIndex j (p.castSucc + 1)))}
          {z : ℂ | Sbtw ℝ
            (polygon.vertex (kwChordPrefixIndex j s.castSucc)) z
            (polygon.vertex (kwChordPrefixIndex j (s.castSucc + 1)))}
        rw [kwChordPrefixIndex_castSucc_add_one,
          kwChordPrefixIndex_castSucc_add_one]
        exact polygon.edgeInteriors_disjoint _ _ hpNe

end StatMech.FrontierA
