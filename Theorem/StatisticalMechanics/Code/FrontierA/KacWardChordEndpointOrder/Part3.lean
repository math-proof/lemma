/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardChordEndpointOrder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardChordEndpointOrder.Part2


namespace StatMech.FrontierA

theorem KWFiniteSimplePolygon.cleanChordEndpointOddFullTurn_of_endpointOrder
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 1 ≤ j.val)
    (horder : polygon.CleanChordEndpointOrder j hj) :
    polygon.CleanChordEndpointOddFullTurn j hj := by
  let p := polygon.edgeList.take j.val
  let q := polygon.edgeList.drop j.val
  let chord := polygon.vertex j - polygon.vertex 0
  have hpne : p ≠ [] := by
    intro h
    rw [List.take_eq_nil_iff] at h
    rcases h with hzero | hempty
    · omega
    · have hlen := congrArg List.length hempty
      simp [KWFiniteSimplePolygon.edgeList] at hlen
      omega
  have hqne : q ≠ [] := by
    intro h
    rw [List.drop_eq_nil_iff] at h
    simp [KWFiniteSimplePolygon.edgeList] at h
    exact (Nat.not_le_of_lt j.isLt) h
  have hj0 : j ≠ 0 := by
    apply Fin.ne_of_val_ne
    simpa using (show j.val ≠ 0 by omega)
  have hchord : chord ≠ 0 := by
    exact sub_ne_zero.mpr (polygon.vertex_injective.ne hj0)
  have hne : kwChordBoundaryTurnDiscrepancy
      (p.getLast hpne) (q.head hqne)
      (q.getLast hqne) (p.head hpne) chord ≠ 0 := by
    simpa only [KWFiniteSimplePolygon.CleanChordEndpointOrder,
      p, q, chord] using horder
  have hodd := (kwChordBoundaryTurnDiscrepancy_odd_iff_ne_zero
    (p.getLast hpne) (q.head hqne) (q.getLast hqne)
    (p.head hpne) chord hchord).mpr hne
  simpa only [KWFiniteSimplePolygon.CleanChordEndpointOddFullTurn,
    p, q, chord] using hodd


theorem KWFiniteSimplePolygon.cleanChordBoundaryPhaseCompatible_of_oddFullTurn
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (j : Fin n) (hj : 1 ≤ j.val)
    (hturn : polygon.CleanChordEndpointOddFullTurn j hj) :
    polygon.CleanChordBoundaryPhaseCompatible j hj := by
  let p := polygon.edgeList.take j.val
  let q := polygon.edgeList.drop j.val
  let chord := polygon.vertex j - polygon.vertex 0
  have hpne : p ≠ [] := by
    intro h
    rw [List.take_eq_nil_iff] at h
    rcases h with hzero | hempty
    · omega
    · have hlen := congrArg List.length hempty
      simp [KWFiniteSimplePolygon.edgeList] at hlen
      omega
  have hqne : q ≠ [] := by
    intro h
    rw [List.drop_eq_nil_iff] at h
    simp [KWFiniteSimplePolygon.edgeList] at h
    exact (Nat.not_le_of_lt j.isLt) h
  have hturn' : kwChordBoundaryTurnDiscrepancy
          (p.getLast hpne) (q.head hqne)
          (q.getLast hqne) (p.head hpne) chord = 2 * Real.pi ∨
      kwChordBoundaryTurnDiscrepancy
          (p.getLast hpne) (q.head hqne)
          (q.getLast hqne) (p.head hpne) chord = -(2 * Real.pi) := by
    simpa only [KWFiniteSimplePolygon.CleanChordEndpointOddFullTurn,
      p, q, chord] using hturn
  have hboundary := kwVectorTurnPhase_chord_boundary_of_odd_full_turn
    (p.getLast hpne) (q.head hqne) (q.getLast hqne)
    (p.head hpne) chord hturn'
  simpa only [KWFiniteSimplePolygon.CleanChordBoundaryPhaseCompatible,
    p, q, chord] using hboundary

end StatMech.FrontierA
