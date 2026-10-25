/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part8
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripExteriorPeriod.Part2


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

theorem hexCSBrickRadius_pos (T L : ℕ) :
    0 < hexCSBrickRadius T L := by
  simp [hexCSBrickRadius]


theorem hexCS_outsideRel_bounds
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    -(hexCSBrickRadius T L : ℤ) < (hexCSOutsideRel e).1 ∧
      (hexCSOutsideRel e).1 < (hexCSBrickRadius T L : ℤ) ∧
      -(hexCSBrickRadius T L : ℤ) < (hexCSOutsideRel e).2 ∧
      (hexCSOutsideRel e).2 < (hexCSBrickRadius T L : ℤ) := by
  have hc := (hexCS_mem_vertexSet_iff T L e.vtx.1).1 e.vtx.2
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexCSBrickRadius, hexCSInStrip, hexAWBookRe2,
      hexAWDepth, hexAWLong, hexAWTrans] at hc hb ⊢ <;> omega


theorem hexCS_left_outsideRel_sign
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hc : e.vtx.1.color = .black) (hedge : e.edge = 0) :
    (0 ≤ hexAWTrans e.vtx.1 → 0 < (hexCSOutsideRel e).2) ∧
      (¬ 0 ≤ hexAWTrans e.vtx.1 →
        (hexCSOutsideRel e).2 < 0) := by
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexAWTrans, hexAWDepth, hexAWLong] at hc hedge hb ⊢
  constructor <;> intro hs
  · by_contra hstrict
    have hzero : i = 0 ∧ j = 0 := by omega
    apply hne
    rw [HexIncidence.mk.injEq]
    constructor
    · apply Subtype.ext
      simp [hexCSStartIncidence, hexCSOrigin, hexAWOriginCoord,
        hzero.1, hzero.2]
    · rfl
  · omega


theorem hexCS_slant_outsideRel_sign
    {T L : ℕ} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    (e.vtx.1.color = .white ∧ e.edge = 1 →
        0 < (hexCSOutsideRel e).2) ∧
      (e.vtx.1.color = .white ∧ e.edge = 2 →
        (hexCSOutsideRel e).2 < 0) := by
  have hc := (hexCS_mem_vertexSet_iff T L e.vtx.1).1 e.vtx.2
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexCSInStrip, hexAWBookRe2,
      hexAWDepth, hexAWLong] at hc hb ⊢ <;> omega

theorem hexCS_right_zero_height_x_neg
    {T L : ℕ} {hT : 0 < T} (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hc : e.vtx.1.color = .white) (hedge : e.edge = 0)
    (hy : (hexCSOutsideRel e).2 = 0) :
    (hexCSOutsideRel e).1 < 0 := by
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSOutsideRel, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexAWDepth, hexAWLong] at hc hedge hy hb ⊢ <;> omega


end
end StatMech.Universality
