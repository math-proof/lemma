/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordEndpointOrder.Part2


namespace StatMech.FrontierA

def KWFiniteSimplePolygon.CleanChordEndpointOddFullTurn
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
  kwChordBoundaryTurnDiscrepancy
      (p.getLast hpne) (q.head hqne)
      (q.getLast hqne) (p.head hpne) chord = 2 * Real.pi ∨
    kwChordBoundaryTurnDiscrepancy
      (p.getLast hpne) (q.head hqne)
      (q.getLast hqne) (p.head hpne) chord = -(2 * Real.pi)


def KWFiniteSimplePolygon.CleanChordEndpointOrder
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
  kwChordBoundaryTurnDiscrepancy
      (p.getLast hpne) (q.head hqne)
      (q.getLast hqne) (p.head hpne) chord ≠ 0


end StatMech.FrontierA
