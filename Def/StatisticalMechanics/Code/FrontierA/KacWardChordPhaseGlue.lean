/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordPhaseGlue.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordSplit.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue


namespace StatMech.FrontierA

def KWFiniteSimplePolygon.CleanChordBoundaryPhaseCompatible
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 1 ≤ j.val) : Prop :=
  let p := polygon.edgeList.take j.val
  let q := polygon.edgeList.drop j.val
  let hpne : p ≠ [] := by
    intro h
    rw [List.take_eq_nil_iff] at h
    rcases h with hzero | hempty
    · omega
    · have hlen := congrArg List.length hempty
      simp [KWFiniteSimplePolygon.edgeList] at hlen
      omega
  let hqne : q ≠ [] := by
    intro h
    rw [List.drop_eq_nil_iff] at h
    simp [KWFiniteSimplePolygon.edgeList] at h
    exact (Nat.not_le_of_lt j.isLt) h
  let chord := polygon.vertex j - polygon.vertex 0
  kwVectorTurnPhase (p.getLast hpne) (q.head hqne) *
      kwVectorTurnPhase (q.getLast hqne) (p.head hpne) =
    -(kwVectorTurnPhase (p.getLast hpne) (-chord) *
        kwVectorTurnPhase (-chord) (p.head hpne) *
      (kwVectorTurnPhase (q.getLast hqne) chord *
        kwVectorTurnPhase chord (q.head hqne)))


end StatMech.FrontierA
