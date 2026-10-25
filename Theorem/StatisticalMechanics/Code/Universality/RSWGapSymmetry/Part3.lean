/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWGapSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Def.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part2
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

theorem rlc_mem_axisGapEdges_of_edgeBoxIncidentGap {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {e : Sym2 (Site 2)}
    (he : rlc_edgeBoxIncidentGap G e) :
    e ∈ rlc_axisGapEdges G := by
  rw [rlc_axisGapEdges, Finset.mem_union]
  left
  rw [Finset.mem_filter]
  refine ⟨?_, he.2⟩
  rw [mem_edgesWithinFinset]
  induction e using Sym2.inductionOn with
  | _ v w =>
      have hv : v ∈ rlc_connectorBox n := by
        simpa [rlc_connectorBox] using
          he.1 v (Sym2.mem_mk_left v w)
      have hw : w ∈ rlc_connectorBox n := by
        simpa [rlc_connectorBox] using
          he.1 w (Sym2.mem_mk_right v w)
      exact ⟨v, hv, w, hw, rfl⟩


theorem rlc_mem_axisGapEdges_of_flipX_edgeBoxIncidentGap {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {e : Sym2 (Site 2)}
    (he : rlc_edgeBoxIncidentGap G (e.map rlc_flipX)) :
    e ∈ rlc_axisGapEdges G := by
  exact (rlc_axisGapEdges_mem_map_flipX_iff G e).mpr
    (rlc_mem_axisGapEdges_of_edgeBoxIncidentGap G he)


theorem rlc_mem_exposed_union_mixedAxisGapEdges_iff {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (e : Sym2 (Site 2)) :
    e ∈ (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
        rlc_mixedAxisGapEdges G ↔
      e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨
      e ∈ rlc_axisGapEdges G ∨
      e ∈ rlc_reflectedPathEdges gamma.1 ∨
      e ∈ rlc_reflectedPathEdges gamma'.1 := by
  simp only [rlc_mixedAxisGapEdges, Finset.mem_union, Finset.mem_sdiff]
  tauto


theorem rlc_axisGapEdge_mem_exposed_union_mixedAxisGapEdges {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {e : Sym2 (Site 2)}
    (he : e ∈ rlc_axisGapEdges G) :
    e ∈ (rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∪
      rlc_mixedAxisGapEdges G := by
  rw [rlc_mem_exposed_union_mixedAxisGapEdges_iff G e]
  exact Or.inr (Or.inl he)


theorem rlc_axisGapEdge_mem_mixedAxisGapEdges_of_not_exposed {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') {e : Sym2 (Site 2)}
    (he : e ∈ rlc_axisGapEdges G)
    (hnot : e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    e ∈ rlc_mixedAxisGapEdges G := by
  rw [rlc_mixedAxisGapEdges, Finset.mem_sdiff]
  exact ⟨by simp [he], hnot⟩


theorem rlc_gapSymmetry_pimsEdgeEquiv_reflected_faceBoundaryEdge
    (S : Set (Site 2)) {f g : Site 2}
    (hfg : (faceBoundaryGraph S).Adj f g) :
    rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) =
      sharedPrimalEdge f g := by
  exact rlc_pimsEdgeEquiv_reflected_mk_of_adj hfg.1


theorem rlc_gapSymmetry_faceBoundary_preimage_not_exposed {n : ℤ}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g) :
    rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
  intro hexposed
  rw [rlc_gapSymmetry_pimsEdgeEquiv_reflected_faceBoundaryEdge
    (rlc_mixedWiredReachSet G omega) hfg] at hexposed
  obtain ⟨p, q, hpq, hadj⟩ := sharedPrimalEdge_isLatticeEdge hfg.1
  have hpqBoundary : (p, q) ∈
      edgeBoundary 2 (rlc_mixedWiredReachSet G omega) := by
    refine ⟨hadj, ?_⟩
    rw [← bdEdge_mk]
    simpa [hpq] using hfg.2
  have hclosed := rlc_mixedWiredReachSet_edgeBoundary_closed
    G hn hlt omega hpqBoundary
  have hopen : rlc_wiredConnectorConfig gamma gamma'
      (rlc_mixedAxisGapEdges G) omega (sharedPrimalEdge f g) = true := by
    simp [rlc_wiredConnectorConfig, hexposed]
  rw [hpq] at hopen
  rw [hopen] at hclosed
  simp at hclosed


theorem rlc_mixedWired_faceBoundary_preimage_mem_mixedAxisGapEdges_iff
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {f g : Site 2}
    (hfg : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Adj f g) :
    rlc_pimsEdgeEquiv s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_mixedAxisGapEdges G ↔
      sharedPrimalEdge f g ∈ rlc_axisGapEdges G ∨
      sharedPrimalEdge f g ∈ rlc_reflectedPathEdges gamma.1 ∨
      sharedPrimalEdge f g ∈ rlc_reflectedPathEdges gamma'.1 := by
  have hpims := rlc_gapSymmetry_pimsEdgeEquiv_reflected_faceBoundaryEdge
    (rlc_mixedWiredReachSet G omega) hfg
  have hnot : sharedPrimalEdge f g ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
    rw [← hpims]
    exact rlc_gapSymmetry_faceBoundary_preimage_not_exposed
      G hn hlt omega hfg
  rw [hpims]
  simp only [rlc_mixedAxisGapEdges, Finset.mem_sdiff, Finset.mem_union]
  have hnot' : ¬(sharedPrimalEdge f g ∈ rlc_pathEdges gamma.1 ∨
      sharedPrimalEdge f g ∈ rlc_pathEdges gamma'.1) := by
    simpa only [Finset.mem_union] using hnot
  constructor
  · rintro ⟨hsupport, _⟩
    rcases hsupport with (hgap | hright) | hleft
    · exact Or.inl hgap
    · exact Or.inr (Or.inl hright)
    · exact Or.inr (Or.inr hleft)
  · intro hsupport
    refine ⟨?_, hnot'⟩
    rcases hsupport with hgap | hright | hleft
    · exact Or.inl (Or.inl hgap)
    · exact Or.inl (Or.inr hright)
    · exact Or.inr hleft


end Universality
end StatMech
