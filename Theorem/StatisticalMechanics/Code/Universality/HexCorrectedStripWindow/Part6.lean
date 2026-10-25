/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExit
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part6


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

theorem hexCSBrickDirections_displacement
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge)) :
    ons_pathDisplacement (hexCSBrickDirections 1 ts) =
      hexCSEndDelta e := by
  have hcoordlast :
      (hexCSCoordPath hexCSOutsideStartCoord
        (hexCSHeadingFin 1) ts).getLast? =
        some (hexAWNeighbor e.vtx.1 e.edge) := by
    rw [hexCSCoordPath_eq_prefixCoords ts hadm.1.1]
    rw [List.getLast?_eq_getLast (by simp)]
    rw [List.getLast_cons (by simp), List.getLast_ofFn (by simp)]
    apply congrArg some
    convert hexCS_finalPrefixCoord_eq_outside e ts he hne hadm using 1 <;>
      simp
  have hb := hexCSCoordPath_brick hexCSOutsideStartCoord 1 ts
    hexCSHeadingFits_start hadm.1.1
  have hg := congrArg List.getLast? hb
  simp only [List.getLast?_map, hcoordlast,
    Option.map_some, ons_pathVertices_getLast] at hg
  exact (Option.some.inj hg).symm


theorem hexCS_inside_brick_depth_pos
    {T L : ℕ} (c : HexAWCoord) (hc : c ∈ hexCSVertexSet T L) :
    0 < (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).2 -
      (hexBrickPos c - hexBrickPos hexCSOutsideStartCoord).1 := by
  rw [hexCS_mem_vertexSet_iff] at hc
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp only [hexCSInStrip, hexAWBookRe2, hexAWDepth,
      hexAWLong] at hc
  all_goals
    simp [hexBrickPos, hexCSOutsideStartCoord]
    omega


theorem hexCSEndDelta_bounds
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L)
    (he : e ∈ hexCSBoundaryIncidences T L) :
    let R : ℤ := hexCSBrickRadius T L
    (-R < (hexCSEndDelta e).1 ∧
      (hexCSEndDelta e).1 < R ∧
      -R < (hexCSEndDelta e).2 ∧
      (hexCSEndDelta e).2 < R) := by
  have hc := (hexCS_mem_vertexSet_iff T L e.vtx.1).1 e.vtx.2
  have hb := hexCS_boundary_classification e he
  rcases e with ⟨⟨⟨i, j, color⟩, hv⟩, edge⟩
  cases color <;> fin_cases edge <;>
    simp [hexCSEndDelta, hexBrickPos, hexCSOutsideStartCoord,
      hexAWNeighbor, hexCSBrickRadius, hexCSInStrip, hexAWBookRe2,
      hexAWDepth, hexAWLong, hexAWTrans] at hc hb ⊢ <;> omega


theorem hexCSBrickDirections_dropLast_mem_cases
    {T L : ℕ} {hT : 0 < T}
    (e : HexCSIncidence T L) (ts : List ℤ)
    (he : e ∈ hexCSBoundaryIncidences T L)
    (hne : e ≠ hexCSStartIncidence T L hT)
    (hadm : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 ts).StaysIn
        (hexCSFiniteRegion T L hT).inRegion ∧
      (ofTurns hexAWStart 1 ts).EndsAt
        (hexAWMid e.vtx.1 e.edge))
    (z : ℤ × ℤ)
    (hz : z ∈ (ons_pathVertices
      (hexCSBrickDirections 1 ts)).dropLast) :
    z = 0 ∨ ∃ c : HexAWCoord, c ∈ hexCSVertexSet T L ∧
      z = hexBrickPos c - hexBrickPos hexCSOutsideStartCoord := by
  have hfull := hexCSBrickDirections_vertices_nodup e ts he hne hadm
  have hend : hexCSEndDelta e ∉
      (ons_pathVertices (hexCSBrickDirections 1 ts)).dropLast := by
    rw [← hexCSBrickDirections_displacement e ts he hne hadm]
    exact ons_pathDisplacement_not_mem_dropLast_of_vertices_nodup _ hfull
  have hzfull : z ∈ ons_pathVertices (hexCSBrickDirections 1 ts) :=
    List.mem_of_mem_dropLast hz
  have hb := hexCSCoordPath_brick hexCSOutsideStartCoord 1 ts
    hexCSHeadingFits_start hadm.1.1
  rw [← hb] at hzfull
  obtain ⟨q, hq, hqz⟩ := List.mem_map.mp hzfull
  rcases hexCSCoordPath_mem_cases e ts he hne hadm q hq with
      hstart | hin | hout
  · left
    rw [← hqz, hstart]
    exact sub_self _
  · right
    exact ⟨q, hin, hqz.symm⟩
  · exfalso
    apply hend
    have hze : z = hexCSEndDelta e := by
      rw [← hqz, hout]
      rfl
    rw [← hze]
    exact hz


end
end StatMech.Universality
