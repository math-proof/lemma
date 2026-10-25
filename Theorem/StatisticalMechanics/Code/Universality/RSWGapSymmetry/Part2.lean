/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Def.StatisticalMechanics.Code.Universality.RSWGapSymmetry
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

theorem rlc_axisGapRegionSet_mem_flipX {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {z : Site 2}
    (hz : z ∈ rlc_axisGapRegionSet G) :
    rlc_flipX z ∈ rlc_axisGapRegionSet G := by
  obtain ⟨hzAllowed, hsAllowed, hreach⟩ := hz
  have hzAllowed' : rlc_flipX z ∈ rlc_connectorAllowed gamma gamma' :=
    (rlc_connectorAllowed_mem_flipX_iff gamma gamma' z).mp hzAllowed
  have hreach' := hreach.map (rlc_axisGapFlipHom G)
  refine ⟨hzAllowed', hsAllowed, ?_⟩
  simpa [rlc_axisGapFlipHom, RlcAxisBarrierGap.seedVertex,
    rlc_flipX, rlc_flipXFun] using hreach'

theorem rlc_axisGapRegionSet_mem_flipX_iff {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (z : Site 2) :
    z ∈ rlc_axisGapRegionSet G ↔
      rlc_flipX z ∈ rlc_axisGapRegionSet G := by
  constructor
  · exact rlc_axisGapRegionSet_mem_flipX G
  · intro hz
    simpa using rlc_axisGapRegionSet_mem_flipX G hz

theorem rlc_axisGapRegion_mem_flipX_iff {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (z : Site 2) :
    z ∈ rlc_axisGapRegion G ↔ rlc_flipX z ∈ rlc_axisGapRegion G := by
  simpa [rlc_axisGapRegion] using rlc_axisGapRegionSet_mem_flipX_iff G z

@[simp] theorem RlcAxisBarrierGap.firstEdge_map_flipX {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') :
    G.firstEdge.map rlc_flipX = G.firstEdge := by
  simp [RlcAxisBarrierGap.firstEdge, RlcAxisBarrierGap.lowerVertex,
    RlcAxisBarrierGap.seedVertex, Sym2.map_mk, rlc_flipX,
    rlc_flipXFun]

@[simp] theorem rlc_edge_map_flipX_involutive (e : Sym2 (Site 2)) :
    (e.map rlc_flipX).map rlc_flipX = e := by
  induction e using Sym2.inductionOn with
  | _ x y => simp [Sym2.map_mk]

theorem rlc_axisGapEdges_mem_map_flipX {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {e : Sym2 (Site 2)}
    (he : e ∈ rlc_axisGapEdges G) :
    e.map rlc_flipX ∈ rlc_axisGapEdges G := by
  rw [rlc_axisGapEdges, Finset.mem_union] at he ⊢
  rcases he with he | he
  · left
    rw [Finset.mem_filter] at he ⊢
    refine ⟨?_, ?_⟩
    · rw [mem_edgesWithinFinset] at he ⊢
      obtain ⟨x, hx, y, hy, rfl⟩ := he.1
      exact ⟨rlc_flipX x, (rlc_connectorBox_mem_flipX_iff x).mp hx,
        rlc_flipX y, (rlc_connectorBox_mem_flipX_iff y).mp hy,
        by simp [Sym2.map_mk]⟩
    · obtain ⟨z, hzRegion, hzEdge⟩ := he.2
      refine ⟨rlc_flipX z,
        (rlc_axisGapRegion_mem_flipX_iff G z).mp hzRegion, ?_⟩
      induction e using Sym2.inductionOn with
      | _ x y =>
          simp only [Sym2.map_mk]
          rw [Sym2.mem_iff] at hzEdge ⊢
          rcases hzEdge with rfl | rfl <;> simp
  · right
    rw [Finset.mem_singleton] at he ⊢
    rw [he, G.firstEdge_map_flipX]

theorem rlc_axisGapEdges_mem_map_flipX_iff {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (e : Sym2 (Site 2)) :
    e ∈ rlc_axisGapEdges G ↔ e.map rlc_flipX ∈ rlc_axisGapEdges G := by
  constructor
  · exact rlc_axisGapEdges_mem_map_flipX G
  · intro he
    simpa using rlc_axisGapEdges_mem_map_flipX G he


end Universality
end StatMech
