/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWArcBadPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWArcJordanCyclic
import Def.StatisticalMechanics.Code.Universality.RSWArcBadPlacement.Part4
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_contourArcRelaxedLocalSide_iff_badEdgesOnOneArc
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u u)
    (hc : c.IsTrail) (hx : x ∈ c.support) (hy : y ∈ c.support) :
    RlcContourArcRelaxedLocalSide G omega c hx hy ↔
      RlcContourRelaxedBadEdgesOnOneArcAt G omega c hx hy := by
  classical
  have hdisjoint :=
    rlc_orderedContourArc_edges_disjoint_complementary c hc hx hy
  constructor
  · intro hside
    rcases hside with hordered | hcomplementary
    · left
      intro f g he hbad
      rcases (rlc_contourArc_edges_cover c hx hy).mp he with hord | hcomp
      · exact False.elim (hbad (hordered hord))
      · exact hcomp
    · right
      intro f g he hbad
      rcases (rlc_contourArc_edges_cover c hx hy).mp he with hord | hcomp
      · exact hord
      · exact False.elim (hbad (hcomplementary hcomp))
  · rintro (hbadComp | hbadOrd)
    · left
      intro f g he
      by_contra hbad
      have hec := rlc_orderedContourArc_edges_subset c hx hy he
      exact hdisjoint he (hbadComp hec hbad)
    · right
      intro f g he
      by_contra hbad
      have hec := rlc_complementaryContourArc_edges_subset c hx hy he
      exact hdisjoint (hbadOrd hec hbad) he


theorem rlc_contourArcRelaxedLocalSide_of_localSide
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2)))
    {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hside : RlcContourArcLocalSide G omega c hx hy) :
    RlcContourArcRelaxedLocalSide G omega c hx hy := by
  rcases hside with hside | hside
  · left
    intro f g he
    exact Or.inr (hside he)
  · right
    intro f g he
    exact Or.inr (hside he)


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {x y : Site 2}
    (a : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk x y)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hlocal : ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
      rlc_contourEdgeRelaxedLocal G f g) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  have hsupport : ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
          rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨
        (s(rlc_dualReflect f, rlc_dualReflect g) ∈
            rlc_mixedAxisGapEdges G ∧
          sharedPrimalEdge f g ∈ rlc_mixedAxisGapEdges G) := by
    intro f g he
    rcases hlocal he with hexposed | hpaired
    · exact Or.inl hexposed
    · have hfg := a.adj_of_mem_edges he
      obtain ⟨htarget, hsource⟩ :=
        rlc_mixedWired_reflected_faceBoundaryEdge_support_of_local
          G hn hlt omega hfg hpaired.1 hpaired.2
      rw [Finset.mem_union] at htarget
      rcases htarget with hexposed | hfresh
      · exact Or.inl hexposed
      · have hsource' := hsource
        rw [rlc_pimsEdgeEquiv_reflected_faceBoundaryEdge
          (rlc_mixedWiredReachSet G omega) hfg] at hsource'
        exact Or.inr ⟨hfresh, hsource'⟩
  obtain ⟨q, _hqEdges, hqSupport⟩ :=
    rlc_dualReflect_wired_faceBoundaryWalk_of_relaxed_support
      G hn hlt omega a hsupport
  have htargetLocal : ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
      rlc_reflectedTargetLocallySupported G
        s(rlc_dualReflect f, rlc_dualReflect g) := by
    intro f g he
    rcases hlocal he with hexposed | hpaired
    · exact Or.inl hexposed
    · exact hpaired.1
  have haBox : ∀ z ∈ a.support,
      rlc_dualReflect z ∈ rlc_connectorBox n :=
    rlc_faceBoundaryArc_reflected_support_mem_connectorBox_of_targetLocal
      G a hyPath htargetLocal
  have hreflectedBox :=
    rlc_faceBoundaryWalk_reflected_support_mem_connectorBox
      G hn hlt omega a haBox
  apply rlc_mixedWiredConnectorEvent_of_openWalk_meets_paths
    G (rlc_dualReflectConfig omega) q
  · intro z hz
    apply hreflectedBox z
    rw [← hqSupport]
    exact hz
  · exact ⟨rlc_dualReflect x, q.start_mem_support, hxPath⟩
  · exact ⟨rlc_dualReflect y, q.end_mem_support, hyPath⟩


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalSide
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {u x y : Site 2}
    (c : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hside : RlcContourArcRelaxedLocalSide G omega c hx hy) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  rcases hside with hordered | hcomplementary
  · exact rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc
      G hn hlt omega (rlc_orderedContourArc c hx hy)
        hxPath hyPath hordered
  · exact rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc
      G hn hlt omega (rlc_complementaryContourArc c hx hy)
        hxPath hyPath hcomplementary


end Universality
end StatMech
