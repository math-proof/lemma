/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part7


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

@[simp] theorem hexCSReflectIncidence_invol {T L : ℕ}
    (e : HexCSIncidence T L) :
    hexCSReflectIncidence (hexCSReflectIncidence e) = e := by
  cases e with
  | mk v edge =>
      rw [hexCSReflectIncidence, hexCSReflectIncidence,
        HexIncidence.mk.injEq]
      exact ⟨hexCSReflectVertex_invol v, hexAWReflectEdge_invol edge⟩

theorem hexCSIsInterior_reflect_iff {T L : ℕ}
    (e : HexCSIncidence T L) :
    hexCSIsInterior (hexCSReflectIncidence e) ↔ hexCSIsInterior e := by
  unfold hexCSIsInterior hexCSReflectIncidence hexCSReflectVertex
  change hexAWNeighbor (hexAWReflectCoord e.vtx.1)
      (hexAWReflectEdge e.edge) ∈ hexCSVertexSet T L ↔
    hexAWNeighbor e.vtx.1 e.edge ∈ hexCSVertexSet T L
  rw [← hexAWReflectCoord_neighbor, hexCSVertexSet_reflect_iff]

theorem hexCSReflectIncidence_mem_boundary_iff {T L : ℕ}
    (e : HexCSIncidence T L) :
    hexCSReflectIncidence e ∈ hexCSBoundaryIncidences T L ↔
      e ∈ hexCSBoundaryIncidences T L := by
  simp [hexCSIsInterior_reflect_iff]


theorem hexCS_boundary_classification {T L : ℕ}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    (e.vtx.1.color = .black ∧ e.edge = 0 ∧
        hexAWDepth e.vtx.1 = 0) ∨
      (e.vtx.1.color = .white ∧ e.edge = 0 ∧
        hexAWDepth e.vtx.1 = T) ∨
      (e.vtx.1.color = .white ∧ e.edge = 1 ∧
        e.vtx.1.i = L) ∨
      (e.vtx.1.color = .white ∧ e.edge = 2 ∧
        e.vtx.1.j = L) := by
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  rw [hexCS_mem_boundary_iff] at he
  unfold hexCSIsInterior at he
  rw [hexCS_mem_vertexSet_iff] at he
  have hc := (hexCS_mem_vertexSet_iff T L ⟨i, j, color⟩).1 hv
  cases color <;> fin_cases edge
  · left
    refine ⟨rfl, rfl, ?_⟩
    change -(i + j) = 0
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong, hexAWNeighbor] at hc he
    omega
  · exfalso
    apply he
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong, hexAWNeighbor] at hc ⊢
    omega
  · exfalso
    apply he
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong, hexAWNeighbor] at hc ⊢
    omega
  · right; left
    refine ⟨rfl, rfl, ?_⟩
    change -(i + j) = (T : ℤ)
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong, hexAWNeighbor] at hc he
    omega
  · right; right; left
    refine ⟨rfl, rfl, ?_⟩
    change i = (L : ℤ)
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong, hexAWNeighbor] at hc he
    omega
  · right; right; right
    refine ⟨rfl, rfl, ?_⟩
    change j = (L : ℤ)
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong, hexAWNeighbor] at hc he
    omega


theorem hexCS_mem_boundary_of_classification {T L : ℕ}
    (e : HexCSIncidence T L)
    (he : (e.vtx.1.color = .black ∧ e.edge = 0 ∧
          hexAWDepth e.vtx.1 = 0) ∨
        (e.vtx.1.color = .white ∧ e.edge = 0 ∧
          hexAWDepth e.vtx.1 = T) ∨
        (e.vtx.1.color = .white ∧ e.edge = 1 ∧
          e.vtx.1.i = L) ∨
        (e.vtx.1.color = .white ∧ e.edge = 2 ∧
          e.vtx.1.j = L)) :
    e ∈ hexCSBoundaryIncidences T L := by
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  rw [hexCS_mem_boundary_iff]
  unfold hexCSIsInterior
  rw [hexCS_mem_vertexSet_iff]
  have hc := (hexCS_mem_vertexSet_iff T L ⟨i, j, color⟩).1 hv
  cases color <;> fin_cases edge <;>
    simp [hexAWDepth, hexAWLong] at he
  all_goals
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong, hexAWNeighbor] at hc ⊢
    omega


theorem hexCS_boundary_heading_cases {T L : ℕ}
    (e : HexCSIncidence T L) (he : e ∈ hexCSBoundaryIncidences T L) :
    hexAWHeading e.vtx.1 e.edge = 4 ∨
      hexAWHeading e.vtx.1 e.edge = 7 ∨
      hexAWHeading e.vtx.1 e.edge = 3 ∨
      hexAWHeading e.vtx.1 e.edge = 5 := by
  obtain h | h | h | h := hexCS_boundary_classification e he
  · left
    rcases h with ⟨hc, he, _⟩
    simp [hexAWHeading, hc, he]
  · right; left
    rcases h with ⟨hc, he, _⟩
    simp [hexAWHeading, hc, he]
  · right; right; left
    rcases h with ⟨hc, he, _⟩
    simp [hexAWHeading, hc, he]
  · right; right; right
    rcases h with ⟨hc, he, _⟩
    simp [hexAWHeading, hc, he]


end
end StatMech.Universality
