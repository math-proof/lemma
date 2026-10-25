/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part37
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem doubledBoxOriginTouchesEdgeSupport_iff_originIncidentMultiplicity_pos
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    doubledBoxOriginTouchesEdgeSupport n m ↔
      0 < doubledBoxOriginIncidentMultiplicity n m := by
  constructor
  · rintro ⟨e, hme, horigin⟩
    have he : e ∈ doubledBoxOriginIncidentEdges n :=
      (mem_doubledBoxOriginIncidentEdges (n := n)).2 horigin
    have hpos : 0 < m e := Nat.pos_of_ne_zero hme
    have hle :
        m e ≤ doubledBoxOriginIncidentMultiplicity n m := by
      dsimp [doubledBoxOriginIncidentMultiplicity]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) he
    exact lt_of_lt_of_le hpos hle
  · intro hpos
    by_contra hnot
    have hzero :
        doubledBoxOriginIncidentMultiplicity n m = 0 := by
      dsimp [doubledBoxOriginIncidentMultiplicity]
      refine Finset.sum_eq_zero ?_
      intro e he
      by_contra hme
      exact hnot
        ⟨e, hme,
          (mem_doubledBoxOriginIncidentEdges (n := n)).1 he⟩
    simp [hzero] at hpos

set_option linter.style.longLine false in


theorem not_doubledBoxOriginTouchesEdgeSupport_iff_originIncidentMultiplicity_eq_zero
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    ¬ doubledBoxOriginTouchesEdgeSupport n m ↔
      doubledBoxOriginIncidentMultiplicity n m = 0 := by
  rw [doubledBoxOriginTouchesEdgeSupport_iff_originIncidentMultiplicity_pos]
  constructor
  · intro hnot
    exact Nat.eq_zero_of_le_zero (Nat.not_lt.mp hnot)
  · intro hzero hpos
    simp [hzero] at hpos

set_option linter.style.longLine false in


theorem doubledBoxOriginTouchesEdgeSupport_iff_exists_originIncidentEdge
    {n : ℕ} {m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ} :
    doubledBoxOriginTouchesEdgeSupport n m ↔
      ∃ e ∈ doubledBoxOriginIncidentEdges n, m e ≠ 0 := by
  constructor
  · rintro ⟨e, hme, horigin⟩
    exact
      ⟨e, (mem_doubledBoxOriginIncidentEdges (n := n)).2 horigin, hme⟩
  · rintro ⟨e, he, hme⟩
    exact
      ⟨e, hme, (mem_doubledBoxOriginIncidentEdges (n := n)).1 he⟩

end Exact3D
end StatMech
