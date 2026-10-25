/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWContactFreeSourceArc
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisOrContactObstruction.Part2
import Def.StatisticalMechanics.Code.Universality.RSWSourceArcPlacement.Part3
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_failureComplementaryArcEscapes
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hplace : RlcFailureComplementaryArcEscapesDefectCut G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨_t, _f, _g, p, _htLower, _htUpper, _htIn, _htOut,
      _hfg, _hshared, _hanchor, hcarry⟩ := hplace
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_carriesRelaxedTraceArc
    G hn hlt omega p hcarry


theorem not_failureComplementaryArcEscapes_of_dualReflect_failure
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : rlc_dualReflectConfig omega ∉
      rlc_mixedWiredConnectorEvent G) :
    ¬ RlcFailureComplementaryArcEscapesDefectCut G omega := by
  intro hplace
  exact hno
    (rlc_mixedWiredConnectorEvent_dualReflect_of_failureComplementaryArcEscapes
      G hn hlt omega hplace)


theorem rlc_doubleFailure_complementaryArc_trace_or_relaxedLocalDefect
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (hnoReflect :
      rlc_dualReflectConfig omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ (t : ℤ) (f g : Site 2)
      (p : (faceBoundaryGraph
        (rlc_mixedWiredReachSet G omega)).Walk f g),
      G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      (faceBoundaryGraph
        (rlc_mixedWiredReachSet G omega)).Adj f g ∧
      sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧
      s(f, g) ∉ p.edges ∧
      ((∀ x ∈ p.support,
          rlc_dualReflect x ∉ rlc_pathVertices gamma.1) ∨
        (∀ y ∈ p.support,
          rlc_dualReflect y ∉ rlc_pathVertices gamma'.1) ∨
        ∃ a b : Site 2, s(a, b) ∈ p.edges ∧
          ¬ rlc_contourEdgeRelaxedLocal G a b) := by
  classical
  obtain ⟨t, f, g, htLower, htUpper, htIn, htOut,
      hfg, hshared, p, hanchor⟩ :=
    rlc_mixedWiredReachSet_faceBoundaryComplementaryArc_with_anchorAdj
      G omega hno
  refine ⟨t, f, g, p, htLower, htUpper, htIn, htOut,
    hfg, hshared, hanchor, ?_⟩
  by_cases hright : ∃ x ∈ p.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1
  · by_cases hleft : ∃ y ∈ p.support,
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1
    · right
      right
      by_contra hdefect
      have hlocal : ∀ {a b : Site 2}, s(a, b) ∈ p.edges →
          rlc_contourEdgeRelaxedLocal G a b := by
        intro a b hab
        by_contra hbad
        exact hdefect ⟨a, b, hab, hbad⟩
      exact hnoReflect
        (rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalWalk_meets_paths
          G hn hlt omega p hlocal hright hleft)
    · right
      left
      intro y hy hyPath
      exact hleft ⟨y, hy, hyPath⟩
  · left
    intro x hx hxPath
    exact hright ⟨x, hx, hxPath⟩


theorem rlc_doubleFailure_complementaryArc_defectCut
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (hnoReflect :
      rlc_dualReflectConfig omega ∉ rlc_mixedWiredConnectorEvent G) :
    ∃ (t : ℤ) (f g : Site 2)
      (p : (faceBoundaryGraph
        (rlc_mixedWiredReachSet G omega)).Walk f g),
      G.lower ≤ t ∧ t < G.upper ∧
      ![0, t] ∈ rlc_mixedWiredReachSet G omega ∧
      ![0, t + 1] ∉ rlc_mixedWiredReachSet G omega ∧
      (faceBoundaryGraph
        (rlc_mixedWiredReachSet G omega)).Adj f g ∧
      sharedPrimalEdge f g = s(![0, t], ![0, t + 1]) ∧
      s(f, g) ∉ p.edges ∧
      RlcRelaxedLocalDefectsHitTraceSubwalksOf G omega p := by
  obtain ⟨t, f, g, htLower, htUpper, htIn, htOut,
      hfg, hshared, p, hanchor⟩ :=
    rlc_mixedWiredReachSet_faceBoundaryComplementaryArc_with_anchorAdj
      G omega hno
  refine ⟨t, f, g, p, htLower, htUpper, htIn, htOut,
    hfg, hshared, hanchor, ?_⟩
  exact RlcRelaxedLocalDefectsSeparateTraces.hitTraceSubwalksOf
    (rlc_relaxedLocalDefectsSeparateTraces_of_dualReflect_failure
      G hn hlt omega hnoReflect) p


theorem rlc_traceSplitCounterexample_boundary_adj₀₁
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
    (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Adj
        ![-1, -2] ![-1, -1] := by
  apply (faceBoundaryGraph_adj_vert
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)
      (-1) (-1) ?_).symm
  rw [hK, rlc_traceSplitCounterexample_right_vertices]
  simp

theorem rlc_traceSplitCounterexample_boundary_adj₁₂
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
    (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Adj
        ![-1, -1] ![0, -1] := by
  apply (faceBoundaryGraph_adj_horiz
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)
      0 (-1) ?_).symm
  rw [hK, rlc_traceSplitCounterexample_right_vertices]
  simp

theorem rlc_traceSplitCounterexample_boundary_adj₂₃
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hK : rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega =
      (rlc_pathVertices rlc_traceSplitCounterexampleRight.1 : Set (Site 2))) :
    (faceBoundaryGraph
      (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)).Adj
        ![0, -1] ![1, -1] := by
  apply (faceBoundaryGraph_adj_horiz
    (rlc_mixedWiredReachSet rlc_windingSideCounterexampleGap omega)
      1 (-1) ?_).symm
  rw [hK, rlc_traceSplitCounterexample_right_vertices]
  simp


end Universality
end StatMech
