/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part10
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_centralFaceFilledBoundaryContacts_of_flippedIntersection
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hcross : RlcBookFlippedTraceIntersection gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryContacts gamma gamma' rho := by
  let H := rlc_connectorCentralFaceFilledReachSet gamma gamma' rho
  obtain ⟨z, hzRight, hzFlipLeft⟩ := hcross
  have hrightStartFlip :
      rlc_flipX (gamma.1.1 : Site 2) = (gamma.1.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  have hrightStartH : rlc_flipX (gamma.1.1 : Site 2) ∈ H := by
    rw [hrightStartFlip]
    exact rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho
      (rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho
        (rlc_path_start_mem_vertices gamma.1))
  have hzFlipExt :=
    rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair rho hno hzFlipLeft
  have hzFlipOut : rlc_flipX z ∉ H := by
    simpa [H, rlc_connectorCentralFaceFilledReachSet] using hzFlipExt
  obtain ⟨x, hxSupp, hxPath⟩ :=
    rlc_faceBoundary_contact_of_flippedTrace_exit gamma.1 H
      (rlc_path_start_mem_vertices gamma.1) hrightStartH hzRight hzFlipOut
  let u : Site 2 := rlc_flipX z
  have huLeft : u ∈ rlc_pathVertices gamma'.1 := hzFlipLeft
  have huFlipH : rlc_flipX u ∈ H := by
    have huFlip : rlc_flipX u = z := by
      simp [u]
    rw [huFlip]
    exact rlc_connectorCentralFaceReachSet_subset_filled gamma gamma' rho
      (rlc_rightPathVertex_mem_centralFaceReachSet gamma gamma' rho hzRight)
  have hleftEndPath : (gamma'.1.2.1 : Site 2) ∈
      rlc_pathVertices gamma'.1 :=
    rlc_connector_path_end_mem_vertices gamma'.1
  have hleftEndExt :=
    rlc_leftPathVertex_mem_centralFaceExteriorSet_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair rho hno hleftEndPath
  have hleftEndFlip :
      rlc_flipX (gamma'.1.2.1 : Site 2) =
        (gamma'.1.2.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  have hleftEndOut : rlc_flipX (gamma'.1.2.1 : Site 2) ∉ H := by
    rw [hleftEndFlip]
    simpa [H, rlc_connectorCentralFaceFilledReachSet] using hleftEndExt
  obtain ⟨y, hySupp, hyPath⟩ :=
    rlc_faceBoundary_contact_of_flippedTrace_exit gamma'.1 H
      huLeft huFlipH hleftEndPath hleftEndOut
  exact ⟨x, y, hxSupp, hySupp, hxPath, hyPath⟩


theorem rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryContacts gamma gamma' rho := by
  exact rlc_centralFaceFilledBoundaryContacts_of_flippedIntersection
    gamma gamma' hfaith
      (rlc_bookFlippedTraceIntersection_of_faithful gamma gamma' hfaith)
      rho hno


theorem rlc_centralFace_retainedAnchorContactWalk_of_faithful_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
      (x y : Site 2) (hx : x ∈ B.contour.support)
      (hy : y ∈ B.contour.support),
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      B.firstFace ∈
        (rlc_centralFaceContactSubwalk B.contour hx hy).support ∧
      ∀ e ∈ (rlc_centralFaceContactSubwalk B.contour hx hy).edges,
        e ∈ B.contour.edges := by
  classical
  let B := Classical.choice
    (rlc_centralFace_retainedAnchoredBoundary_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair rho hno)
  obtain ⟨x, y, hxSupp, hySupp, hxPath, hyPath⟩ :=
    rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith rho hno
  obtain ⟨x', hxx'⟩ := hxSupp
  obtain ⟨y', hyy'⟩ := hySupp
  have hxe : s(x, x') ∈ B.contour.edges := B.contour_covers _
    (by rw [SimpleGraph.mem_edgeSet]; exact hxx')
  have hye : s(y, y') ∈ B.contour.edges := B.contour_covers _
    (by rw [SimpleGraph.mem_edgeSet]; exact hyy')
  have hx : x ∈ B.contour.support :=
    B.contour.fst_mem_support_of_mem_edges hxe
  have hy : y ∈ B.contour.support :=
    B.contour.fst_mem_support_of_mem_edges hye
  refine ⟨B, x, y, hx, hy, hxPath, hyPath, ?_,
    rlc_centralFaceContactSubwalk_edges_subset B.contour hx hy⟩
  rw [rlc_centralFaceContactSubwalk,
    SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_reverse]
  exact Or.inl (by
    simpa using (B.contour.takeUntil x hx).start_mem_support)


theorem rlc_centralFace_anchorToContacts_of_faithful_failure
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
      (x y : Site 2)
      (px : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          B.firstFace x)
      (py : (faceBoundaryGraph
        (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
          B.firstFace y),
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
        (∀ e ∈ px.edges, e ∈ B.contour.edges) ∧
        ∀ e ∈ py.edges, e ∈ B.contour.edges := by
  obtain ⟨B, x, y, hx, hy, hxPath, hyPath, _hanchor, _hedges⟩ :=
    rlc_centralFace_retainedAnchorContactWalk_of_faithful_failure
      gamma gamma' hfaith rho hno
  let px := B.contour.takeUntil x hx
  let py := B.contour.takeUntil y hy
  refine ⟨B, x, y, px, py, hxPath, hyPath, ?_, ?_⟩
  · intro e he
    exact B.contour.edges_takeUntil_subset hx he
  · intro e he
    exact B.contour.edges_takeUntil_subset hy he


theorem rlc_contourContactArcs_support_cover
    {H : SimpleGraph (Site 2)} {u x y z : Site 2}
    (c : H.Walk u u) (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hz : z ∈ c.support) :
    z ∈ (rlc_orderedContourArc c hx hy).support ∨
      z ∈ (rlc_complementaryContourArc c hx hy).support := by
  classical
  let hy' : y ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy
  have hzrot : z ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hz
  rw [← SimpleGraph.Walk.take_spec (c.rotate x hx) hy',
    SimpleGraph.Walk.mem_support_append_iff] at hzrot
  rcases hzrot with hprefix | hsuffix
  · exact Or.inl (by
      simpa [rlc_orderedContourArc, hy'] using hprefix)
  · exact Or.inr (by
      simpa [rlc_complementaryContourArc, hy',
        SimpleGraph.Walk.support_reverse] using hsuffix)


theorem rlc_contourContactArcs_edges_decompose
    {H : SimpleGraph (Site 2)} {u x y : Site 2}
    (c : H.Walk u u) (hx : x ∈ c.support) (hy : y ∈ c.support) :
    (c.rotate x hx).edges =
      (rlc_orderedContourArc c hx hy).edges ++
        (rlc_complementaryContourArc c hx hy).edges.reverse := by
  let hy' : y ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy
  rw [← SimpleGraph.Walk.take_spec (c.rotate x hx) hy',
    SimpleGraph.Walk.edges_append]
  simp [rlc_orderedContourArc, rlc_complementaryContourArc, hy',
    SimpleGraph.Walk.edges_reverse]


theorem rlc_contourContactArcs_edges_cover
    {H : SimpleGraph (Site 2)} {u x y : Site 2}
    (c : H.Walk u u) (hx : x ∈ c.support) (hy : y ∈ c.support)
    {e : Sym2 (Site 2)} (he : e ∈ c.edges) :
    e ∈ (rlc_orderedContourArc c hx hy).edges ∨
      e ∈ (rlc_complementaryContourArc c hx hy).edges := by
  have heRot : e ∈ (c.rotate x hx).edges :=
    (SimpleGraph.Walk.rotate_edges c x hx).perm.mem_iff.mpr he
  rw [rlc_contourContactArcs_edges_decompose c hx hy,
    List.mem_append, List.mem_reverse] at heRot
  exact heRot


theorem rlc_contourContactArcs_edges_disjoint
    {H : SimpleGraph (Site 2)} {u x y : Site 2}
    (c : H.Walk u u) (hc : c.IsTrail)
    (hx : x ∈ c.support) (hy : y ∈ c.support) :
    List.Disjoint (rlc_orderedContourArc c hx hy).edges
      (rlc_complementaryContourArc c hx hy).edges := by
  have hnodup : (c.rotate x hx).edges.Nodup :=
    (hc.rotate hx).edges_nodup
  rw [rlc_contourContactArcs_edges_decompose c hx hy,
    List.nodup_append] at hnodup
  intro e heOrdered heComplementary
  exact hnodup.2.2 e heOrdered e (List.mem_reverse.mpr heComplementary) rfl


theorem rlc_orderedContourArc_isPath
    {H : SimpleGraph (Site 2)} {u x y : Site 2}
    (c : H.Walk u u) (hc : c.IsCycle)
    (hx : x ∈ c.support) (hy : y ∈ c.support) :
    (rlc_orderedContourArc c hx hy).IsPath := by
  let hy' : y ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy
  exact (hc.rotate hx).isPath_takeUntil hy'


theorem rlc_complementaryContourArc_isPath
    {H : SimpleGraph (Site 2)} {u x y : Site 2}
    (c : H.Walk u u) (hc : c.IsCycle)
    (hx : x ∈ c.support) (hy : y ∈ c.support) (hxy : x ≠ y) :
    (rlc_complementaryContourArc c hx hy).IsPath := by
  let hy' : y ∈ (c.rotate x hx).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff c x hx).2 hy
  have hcycle : (((c.rotate x hx).takeUntil y hy').append
      ((c.rotate x hx).dropUntil y hy')).IsCycle := by
    rw [SimpleGraph.Walk.take_spec]
    exact hc.rotate hx
  have htake : ¬ ((c.rotate x hx).takeUntil y hy').Nil :=
    SimpleGraph.Walk.not_nil_of_ne hxy
  have hdrop : ((c.rotate x hx).dropUntil y hy').IsPath :=
    SimpleGraph.Walk.IsCycle.isPath_of_append_right htake hcycle
  exact (SimpleGraph.Walk.isPath_reverse_iff _).2 hdrop


end
end StatMech.Universality
