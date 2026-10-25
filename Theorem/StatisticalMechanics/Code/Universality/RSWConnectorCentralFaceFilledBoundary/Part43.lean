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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part39
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_negativeStrictEntry_reachableLeft_or_prefixAvoidsOriginalContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    (hentry : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    (∃ y : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace y ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      RlcCentralFaceNegativeStrictEntryPrefixAvoidsOriginalContactAt
        gamma gamma' rho L q := by
  obtain ⟨A, a, b, pA, p, r, hab, hdecomp, hAzero, hAoff,
    hentryNot, hrNeg, hrNoLeft, hrRight, hrNotNil⟩ := hentry
  by_cases hcontact : ∃ y ∈ p.support,
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1
  · left
    obtain ⟨y, hyP, hyPath⟩ := hcontact
    exact ⟨y, ⟨pA.reverse.append (p.takeUntil y hyP)⟩, hyPath⟩
  · right
    refine ⟨A, a, b, pA, p, r, hab, hdecomp, hAzero, hAoff,
      hentryNot, hrNeg, hrNoLeft, hrRight, hrNotNil, ?_⟩
    intro y hyP hyPath
    exact hcontact ⟨y, hyP, hyPath⟩


theorem rlc_positiveStrictEntry_reachableRight_or_prefixAvoidsOriginalContact
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u}
    (hentry : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.secondFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      RlcCentralFacePositiveStrictEntryPrefixAvoidsOriginalContactAt
        gamma gamma' rho L q := by
  obtain ⟨A, a, b, pA, p, r, hanchor, hab, hdecomp, hAzero,
    hAstart, hentryNot, hrPos, hrNoRight, hrLeft, hrNotNil⟩ := hentry
  by_cases hcontact : ∃ x ∈ p.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1
  · left
    obtain ⟨x, hxP, hxPath⟩ := hcontact
    exact ⟨x, ⟨hanchor.symm.toWalk.append
      (pA.reverse.append (p.takeUntil x hxP))⟩, hxPath⟩
  · right
    refine ⟨A, a, b, pA, p, r, hanchor, hab, hdecomp, hAzero,
      hAstart, hentryNot, hrPos, hrNoRight, hrLeft, hrNotNil, ?_⟩
    intro x hxP hxPath
    exact hcontact ⟨x, hxP, hxPath⟩


theorem rlc_centralFacePIMS_success_or_strictEntryPrefixAvoidance
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u u' : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    {q' : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u'}
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q') :
    (rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma') ∨
      RlcCentralFaceNegativeStrictEntryPrefixAvoidsOriginalContactAt
        gamma gamma' rho L q ∨
      RlcCentralFacePositiveStrictEntryPrefixAvoidsOriginalContactAt
        gamma gamma' rho L q' := by
  rcases rlc_negativeStrictEntry_reachableLeft_or_prefixAvoidsOriginalContact
      hneg with hleft | hnegAvoid
  · rcases rlc_positiveStrictEntry_reachableRight_or_prefixAvoidsOriginalContact
        hpos with hright | hposAvoid
    · left
      obtain ⟨y, hyReach, hyPath⟩ := hleft
      obtain ⟨x, hxReachSecond, hxPath⟩ := hright
      have hxReach : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable L.boundary.firstFace x :=
        (L.boundary.anchor_mem_goodBoundaryGraph hfaith).reachable.trans
          hxReachSecond
      have hcomponent : RlcCentralFaceFilledBoundaryGoodComponentContacts
          gamma gamma' rho :=
        ⟨x, y, hxReach.symm.trans hyReach, hxPath, hyPath⟩
      exact rlc_centralFacePIMS_success_of_filledBoundaryContactSegment
        gamma gamma' rho
          (rlc_filledBoundaryContactSegment_of_goodComponentContacts
            gamma gamma' rho hcomponent)
    · exact Or.inr (Or.inr hposAvoid)
  · exact Or.inr (Or.inl hnegAvoid)


theorem rlc_centralFacePIMS_success_of_no_strictEntryPrefixAvoidance
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u u' : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    {q' : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u'}
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q')
    (hnegAvoid : ¬ RlcCentralFaceNegativeStrictEntryPrefixAvoidsOriginalContactAt
      gamma gamma' rho L q)
    (hposAvoid : ¬ RlcCentralFacePositiveStrictEntryPrefixAvoidsOriginalContactAt
      gamma gamma' rho L q') :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
      rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  rcases rlc_centralFacePIMS_success_or_strictEntryPrefixAvoidance
      hfaith hneg hpos with hsuccess | hnegResidue | hposResidue
  · exact hsuccess
  · exact (hnegAvoid hnegResidue).elim
  · exact (hposAvoid hposResidue).elim

theorem rlc_positiveStrictWallEntry_of_decomp
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u}
    (h : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    RlcCentralFacePositiveStrictWallEntryAt gamma gamma' rho L u := by
  obtain ⟨A, a, b, pA, p, r, hanchor, hab, hdecomp, hAzero,
    hAstart, hentry, hrPos, hrNoRight, hrLeft, hrNotNil⟩ := h
  exact ⟨A, a, b, p, r, hab, hAzero, hAstart, hentry,
    hrPos, hrNoRight, hrLeft, hrNotNil⟩

theorem rlc_negativeStrictWallEntry_of_decomp
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    (h : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    RlcCentralFaceNegativeStrictWallEntryAt gamma gamma' rho L u := by
  obtain ⟨A, a, b, pA, p, r, hab, hdecomp, hAzero,
    hAoff, hentry, hrNeg, hrNoLeft, hrRight, hrNotNil⟩ := h
  exact ⟨A, a, b, p, r, hab, hAzero, hAoff, hentry,
    hrNeg, hrNoLeft, hrRight, hrNotNil⟩

@[simp] theorem rlc_site_eta (x : Site 2) :
    (![x 0, x 1] : Site 2) = x := by
  exact cons_eq_site rfl rfl

@[simp] theorem rlc_site_mk_eq_site (a b : Int) (x : Site 2) :
    ((![a, b] : Site 2) = x ↔ a = x 0 ∧ b = x 1) := by
  constructor
  · intro h
    subst x
    simp
  · rintro ⟨ha, hb⟩
    exact cons_eq_site ha hb

@[simp] theorem rlc_int_self_ne_add_one (a : Int) : a ≠ a + 1 := by omega

@[simp] theorem rlc_int_self_ne_sub_one (a : Int) : a ≠ a - 1 := by omega

@[simp] theorem rlc_int_add_one_ne_self (a : Int) : a + 1 ≠ a := by omega

@[simp] theorem rlc_int_sub_one_ne_self (a : Int) : a - 1 ≠ a := by omega

@[simp] theorem rlc_int_add_two_ne_self (a : Int) : a + 1 + 1 ≠ a := by omega

@[simp] theorem rlc_int_sub_two_ne_self (a : Int) : a - 1 - 1 ≠ a := by omega

@[simp] theorem rlc_int_self_ne_add_two (a : Int) : a ≠ a + 1 + 1 := by omega

@[simp] theorem rlc_int_self_ne_sub_two (a : Int) : a ≠ a - 1 - 1 := by omega

@[simp] theorem rlc_int_sub_one_ne_add_one (a : Int) : a - 1 ≠ a + 1 := by omega

@[simp] theorem rlc_int_add_one_ne_sub_one (a : Int) : a + 1 ≠ a - 1 := by omega

@[simp] theorem rlc_flankFaces_step_right (x : Site 2) :
    flankFaces x ![x 0 + 1, x 1] =
      s((![x 0, x 1 - 1] : Site 2), x) := by
  simp [flankFaces]

@[simp] theorem rlc_flankFaces_step_left (x : Site 2) :
    flankFaces x ![x 0 - 1, x 1] =
      s((![x 0 - 1, x 1 - 1] : Site 2), ![x 0 - 1, x 1]) := by
  simp [flankFaces] <;> omega

@[simp] theorem rlc_flankFaces_step_top (x : Site 2) :
    flankFaces x ![x 0, x 1 + 1] =
      s((![x 0 - 1, x 1] : Site 2), x) := by
  simp [flankFaces]

@[simp] theorem rlc_flankFaces_step_bottom (x : Site 2) :
    flankFaces x ![x 0, x 1 - 1] =
      s((![x 0 - 1, x 1 - 1] : Site 2), ![x 0, x 1 - 1]) := by
  simp [flankFaces]


theorem rlc_isPath_incident_edge_eq_of_two
    {V : Type*} {G : SimpleGraph V} {start finish x y z w : V}
    (p : G.Walk start finish) (hp : p.IsPath)
    (hxy : s(x, y) ∈ p.edges) (hyz : s(y, z) ∈ p.edges)
    (hxz : x ≠ z) (hyw : s(y, w) ∈ p.edges) :
    w = x ∨ w = z := by
  have hySupport : y ∈ p.support := p.snd_mem_support_of_mem_edges hxy
  obtain ⟨i, hiy, hi⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hySupport
  by_cases hiZero : i = 0
  · have hyStart : y = start := by
      rw [← hiy, hiZero, p.getVert_zero]
    have hxEdge : s(start, x) ∈ p.edges := by
      simpa [hyStart, Sym2.eq_swap] using hxy
    have hzEdge : s(start, z) ∈ p.edges := by
      simpa [hyStart] using hyz
    have hxSnd := hp.eq_snd_of_mem_edges hxEdge
    have hzSnd := hp.eq_snd_of_mem_edges hzEdge
    exact False.elim (hxz (hxSnd.trans hzSnd.symm))
  by_cases hiEnd : i = p.length
  · have hyEnd : y = finish := by
      rw [← hiy, hiEnd, p.getVert_length]
    have hxEdge : s(finish, x) ∈ p.edges := by
      simpa [hyEnd, Sym2.eq_swap] using hxy
    have hzEdge : s(finish, z) ∈ p.edges := by
      simpa [hyEnd] using hyz
    have hxPen := hp.eq_penultimate_of_mem_edges hxEdge
    have hzPen := hp.eq_penultimate_of_mem_edges hzEdge
    exact False.elim (hxz (hxPen.trans hzPen.symm))
  have hiLt : i < p.length := lt_of_le_of_ne hi hiEnd
  have hneighbors := hp.neighborSet_toSubgraph_internal hiZero hiLt
  have mem_neighbors {v : V} (hyv : s(y, v) ∈ p.edges) :
      v ∈ p.toSubgraph.neighborSet (p.getVert i) := by
    rw [SimpleGraph.Subgraph.mem_neighborSet]
    apply p.adj_toSubgraph_iff_mem_edges.mpr
    simpa [hiy] using hyv
  have hxEdge : s(y, x) ∈ p.edges := by
    simpa [Sym2.eq_swap] using hxy
  have hxN := mem_neighbors (v := x) hxEdge
  have hzN := mem_neighbors (v := z) hyz
  have hwN := mem_neighbors (v := w) hyw
  rw [hneighbors] at hxN hzN hwN
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxN hzN hwN
  rcases hxN with hxPrev | hxNext <;>
    rcases hzN with hzPrev | hzNext <;>
    rcases hwN with hwPrev | hwNext
  · exact False.elim (hxz (hxPrev.trans hzPrev.symm))
  · exact False.elim (hxz (hxPrev.trans hzPrev.symm))
  · exact Or.inl (hwPrev.trans hxPrev.symm)
  · exact Or.inr (hwNext.trans hzNext.symm)
  · exact Or.inr (hwPrev.trans hzPrev.symm)
  · exact Or.inl (hwNext.trans hxNext.symm)
  · exact False.elim (hxz (hxNext.trans hzNext.symm))
  · exact False.elim (hxz (hxNext.trans hzNext.symm))


theorem rlc_isPath_exists_other_incident_edge
    {V : Type*} {G : SimpleGraph V} {start finish b c : V}
    (p : G.Walk start finish) (hp : p.IsPath)
    (hbc : s(b, c) ∈ p.edges)
    (hbStart : b ≠ start) (hbFinish : b ≠ finish) :
    ∃ d : V, s(b, d) ∈ p.edges ∧ d ≠ c := by
  have hbSupport : b ∈ p.support := p.fst_mem_support_of_mem_edges hbc
  obtain ⟨i, hib, hi⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hbSupport
  have hiZero : i ≠ 0 := by
    intro hi0
    apply hbStart
    rw [← hib, hi0, p.getVert_zero]
  have hiEnd : i ≠ p.length := by
    intro hil
    apply hbFinish
    rw [← hib, hil, p.getVert_length]
  have hiLt : i < p.length := lt_of_le_of_ne hi hiEnd
  let prev := p.getVert (i - 1)
  let next := p.getVert (i + 1)
  have hprevMem : prev ∈ p.toSubgraph.neighborSet (p.getVert i) := by
    rw [hp.neighborSet_toSubgraph_internal hiZero hiLt]
    exact Set.mem_insert _ _
  have hnextMem : next ∈ p.toSubgraph.neighborSet (p.getVert i) := by
    rw [hp.neighborSet_toSubgraph_internal hiZero hiLt]
    exact Or.inr (Set.mem_singleton _)
  have hprevEdge : s(b, prev) ∈ p.edges := by
    apply p.adj_toSubgraph_iff_mem_edges.mp
    have := (SimpleGraph.Subgraph.mem_neighborSet
      p.toSubgraph (p.getVert i) prev).mp hprevMem
    simpa [hib] using this
  have hnextEdge : s(b, next) ∈ p.edges := by
    apply p.adj_toSubgraph_iff_mem_edges.mp
    have := (SimpleGraph.Subgraph.mem_neighborSet
      p.toSubgraph (p.getVert i) next).mp hnextMem
    simpa [hib] using this
  have hprevNext : prev ≠ next := by
    intro heq
    have hinj := hp.getVert_injOn
      (show i - 1 ≤ p.length by omega)
      (show i + 1 ≤ p.length by omega) heq
    omega
  by_cases hcPrev : c = prev
  · exact ⟨next, hnextEdge, fun h =>
      hprevNext (hcPrev.symm.trans h.symm)⟩
  · exact ⟨prev, hprevEdge, fun h => hcPrev h.symm⟩


theorem rlc_positive_reflectedLeft_third_incident_nonwall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {x y z w : Site 2}
    (hyPos : 0 < y 0)
    (hyNoRight : y ∉ rlc_pathVertices gamma.1)
    (hxy : s(x, y) ∈ rlc_reflectedPathEdges gamma'.1)
    (hyz : s(y, z) ∈ rlc_reflectedPathEdges gamma'.1)
    (hxz : x ≠ z)
    (hywNeX : s(y, w) ≠ s(x, y))
    (hywNeZ : s(y, w) ≠ s(y, z)) :
    s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
  intro hywWall
  have hyNoLeft : y ∉ rlc_pathVertices gamma'.1 := by
    intro hyLeft
    have hyRect := rlc_pathVertex_mem_rect gamma'.1 hyLeft
    rw [mem_rect] at hyRect
    omega
  have hyNoFlipRight : ¬ ∃ q ∈ rlc_pathVertices gamma.1,
      y = rlc_flipX q := by
    rintro ⟨q, hq, hyq⟩
    have hqRect := rlc_pathVertex_mem_rect gamma.1 hq
    rw [mem_rect] at hqRect
    have h0 := congrArg (fun a : Site 2 => a 0) hyq
    change y 0 = -q 0 at h0
    omega
  have hywLeft : s(y, w) ∈ rlc_reflectedPathEdges gamma'.1 :=
    rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
      gamma gamma' hywWall (Sym2.mem_mk_left _ _)
        hyNoRight hyNoLeft hyNoFlipRight
  let W := (rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom
  have hxyW : s(x, y) ∈ W.edges :=
    rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
      gamma'.1 hxy
  have hyzW : s(y, z) ∈ W.edges :=
    rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
      gamma'.1 hyz
  have hywW : s(y, w) ∈ W.edges :=
    rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
      gamma'.1 hywLeft
  rcases rlc_isPath_incident_edge_eq_of_two W
      (rlc_reflectedAmbientCrossingWalk_isPath gamma'.1)
      hxyW hyzW hxz hywW with rfl | rfl
  · exact hywNeX (by simp [Sym2.eq_swap])
  · exact hywNeZ rfl


theorem rlc_negative_reflectedRight_third_incident_nonwall
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {x y z w : Site 2}
    (hyNeg : y 0 < 0)
    (hyNoLeft : y ∉ rlc_pathVertices gamma'.1)
    (hxy : s(x, y) ∈ rlc_reflectedPathEdges gamma.1)
    (hyz : s(y, z) ∈ rlc_reflectedPathEdges gamma.1)
    (hxz : x ≠ z)
    (hywNeX : s(y, w) ≠ s(x, y))
    (hywNeZ : s(y, w) ≠ s(y, z)) :
    s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
  intro hywWall
  have hyNoRight : y ∉ rlc_pathVertices gamma.1 := by
    intro hyRight
    have hyRect := rlc_pathVertex_mem_rect gamma.1 hyRight
    rw [mem_rect] at hyRect
    omega
  have hyNoFlipLeft : ¬ ∃ q ∈ rlc_pathVertices gamma'.1,
      y = rlc_flipX q := by
    rintro ⟨q, hq, hyq⟩
    have hqRect := rlc_pathVertex_mem_rect gamma'.1 hq
    rw [mem_rect] at hqRect
    have h0 := congrArg (fun a : Site 2 => a 0) hyq
    change y 0 = -q 0 at h0
    omega
  have hywRight : s(y, w) ∈ rlc_reflectedPathEdges gamma.1 :=
    rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
      gamma gamma' hywWall (Sym2.mem_mk_left _ _)
        hyNoRight hyNoLeft hyNoFlipLeft
  let W := ((rlc_ambientCrossingWalk gamma.1).map
    rlc_flipXLatticeHom).reverse
  have toW {e : Sym2 (Site 2)}
      (he : e ∈ rlc_reflectedPathEdges gamma.1) : e ∈ W.edges := by
    have hf :=
      rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
        gamma.1 he
    simpa [W, SimpleGraph.Walk.edges_reverse] using hf
  have hxyW := toW hxy
  have hyzW := toW hyz
  have hywW := toW hywRight
  rcases rlc_isPath_incident_edge_eq_of_two W
      (rlc_reflectedAmbientCrossingWalk_isPath gamma.1).reverse
      hxyW hyzW hxz hywW with rfl | rfl
  · exact hywNeX (by simp [Sym2.eq_swap])
  · exact hywNeZ rfl

set_option maxHeartbeats 800000 in


theorem rlc_centralFaceRegion_continue_consecutive_wall_flank
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {x y z h : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y)
    (hyz : (hypercubicLattice 2).Adj y z)
    (hxz : x ≠ z)
    (hyInterior : -2 * n < y 0 ∧ y 0 < 2 * n ∧
      -n < y 1 ∧ y 1 < n)
    (hother : ∀ w : Site 2,
      (hypercubicLattice 2).Adj y w →
      s(y, w) ≠ s(x, y) → s(y, w) ≠ s(y, z) →
      s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces x y) :
    ∃ k ∈ flankFaces y z,
      k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  have sideIff {w f g : Site 2}
      (hyw : (hypercubicLattice 2).Adj y w)
      (hflank : flankFaces y w = s(f, g))
      (hneIn : s(y, w) ≠ s(x, y))
      (hneOut : s(y, w) ≠ s(y, z)) :
      (f ∈ rlc_connectorCentralFaceRegion gamma gamma' ↔
        g ∈ rlc_connectorCentralFaceRegion gamma gamma') := by
    have hnot := hother w hyw hneIn hneOut
    have hf : f ∈ flankFaces y w := by
      rw [hflank, Sym2.mem_iff]
      exact Or.inl rfl
    have hg : g ∈ flankFaces y w := by
      rw [hflank, Sym2.mem_iff]
      exact Or.inr rfl
    have hfBox := rlc_flank_mem_connectorFaceBox_of_interior
      hyw hyInterior hf
    have hgBox := rlc_flank_mem_connectorFaceBox_of_interior
      hyw hyInterior hg
    constructor
    · intro hfRegion
      exact rlc_centralFaceRegion_other_flank_of_nonwall
        gamma gamma' hyw hnot hfRegion hf hg hgBox
    · intro hgRegion
      exact rlc_centralFaceRegion_other_flank_of_nonwall
        gamma gamma' hyw hnot hgRegion hg hf hfBox
  let NE : Site 2 := y
  let NW : Site 2 := ![y 0 - 1, y 1]
  let SW : Site 2 := ![y 0 - 1, y 1 - 1]
  let SE : Site 2 := ![y 0, y 1 - 1]
  have hUp : s(y, ![y 0, y 1 + 1]) ≠ s(x, y) →
      s(y, ![y 0, y 1 + 1]) ≠ s(y, z) →
      (NW ∈ rlc_connectorCentralFaceRegion gamma gamma' ↔
        NE ∈ rlc_connectorCentralFaceRegion gamma gamma') := by
    intro hneIn hneOut
    exact sideIff (by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp)
      (by simpa [NW, NE] using rlc_flankFaces_step_top y)
      hneIn hneOut
  have hLeft : s(y, ![y 0 - 1, y 1]) ≠ s(x, y) →
      s(y, ![y 0 - 1, y 1]) ≠ s(y, z) →
      (SW ∈ rlc_connectorCentralFaceRegion gamma gamma' ↔
        NW ∈ rlc_connectorCentralFaceRegion gamma gamma') := by
    intro hneIn hneOut
    exact sideIff (by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp)
      (by simpa [SW, NW] using rlc_flankFaces_step_left y)
      hneIn hneOut
  have hDown : s(y, ![y 0, y 1 - 1]) ≠ s(x, y) →
      s(y, ![y 0, y 1 - 1]) ≠ s(y, z) →
      (SW ∈ rlc_connectorCentralFaceRegion gamma gamma' ↔
        SE ∈ rlc_connectorCentralFaceRegion gamma gamma') := by
    intro hneIn hneOut
    exact sideIff (by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp)
      (by simpa [SW, SE] using rlc_flankFaces_step_bottom y)
      hneIn hneOut
  have hRight : s(y, ![y 0 + 1, y 1]) ≠ s(x, y) →
      s(y, ![y 0 + 1, y 1]) ≠ s(y, z) →
      (SE ∈ rlc_connectorCentralFaceRegion gamma gamma' ↔
        NE ∈ rlc_connectorCentralFaceRegion gamma gamma') := by
    intro hneIn hneOut
    exact sideIff (by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp)
      (by simpa [SE, NE] using rlc_flankFaces_step_right y)
      hneIn hneOut
  rcases face_adj_dir hxy with rfl | rfl | rfl | rfl <;>
    rcases face_adj_dir hyz with rfl | rfl | rfl | rfl
  all_goals
    simp only [rlc_flankFaces_step_right, rlc_flankFaces_step_left,
      rlc_flankFaces_step_top, rlc_flankFaces_step_bottom] at hh ⊢
    rw [Sym2.mem_iff] at hh
    simp only [Sym2.mem_iff]
    simp [NE, NW, SW, SE, Sym2.eq_iff] at hUp hLeft hDown hRight
    rcases hh with rfl | rfl <;>
      simp [NE, NW, SW, SE] at hhRegion ⊢ <;> tauto


theorem rlc_walk_terminal_regionFlank_of_consecutive_detours
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {b u : Site 2} (q : (hypercubicLattice 2).Walk b u)
    (hqNotNil : ¬ q.Nil)
    (hqInterior : ∀ y ∈ q.support,
      -2 * n < y 0 ∧ y 0 < 2 * n ∧ -n < y 1 ∧ y 1 < n)
    (hthird : ∀ {x y z w : Site 2},
      s(x, y) ∈ q.edges → s(y, z) ∈ q.edges → x ≠ z →
      (hypercubicLattice 2).Adj y w →
      s(y, w) ≠ s(x, y) → s(y, w) ≠ s(y, z) →
      s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma')
    {h : Site 2}
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces b q.snd) :
    ∃ k ∈ flankFaces q.penultimate u,
      k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  induction q generalizing h with
  | nil => exact False.elim (hqNotNil SimpleGraph.Walk.nil_nil)
  | @cons a c u hac t ih =>
      cases t with
      | nil =>
          exact ⟨h, by simpa, hhRegion⟩
      | @cons c d u hcd s =>
          have hacEdge : s(a, c) ∈
              (SimpleGraph.Walk.cons hac (.cons hcd s)).edges := by simp
          have hcdEdge : s(c, d) ∈
              (SimpleGraph.Walk.cons hac (.cons hcd s)).edges := by simp
          have htailEdges : ∀ e ∈ (SimpleGraph.Walk.cons hcd s).edges,
              e ∈ (SimpleGraph.Walk.cons hac (.cons hcd s)).edges := by
            intro e he
            rw [SimpleGraph.Walk.edges_cons]
            exact List.mem_cons_of_mem _ he
          have htailSupport : ∀ y ∈
              (SimpleGraph.Walk.cons hcd s).support,
              y ∈ (SimpleGraph.Walk.cons hac (.cons hcd s)).support := by
            intro y hy
            rw [SimpleGraph.Walk.support_cons]
            exact List.mem_cons_of_mem _ hy
          have htailInterior : ∀ y ∈
              (SimpleGraph.Walk.cons hcd s).support,
              -2 * n < y 0 ∧ y 0 < 2 * n ∧
                -n < y 1 ∧ y 1 < n := by
            intro y hy
            exact hqInterior y (htailSupport y hy)
          have htailThird : ∀ {x y z w : Site 2},
              s(x, y) ∈ (SimpleGraph.Walk.cons hcd s).edges →
              s(y, z) ∈ (SimpleGraph.Walk.cons hcd s).edges →
              x ≠ z → (hypercubicLattice 2).Adj y w →
              s(y, w) ≠ s(x, y) → s(y, w) ≠ s(y, z) →
              s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
            intro x y z w hxy hyz hxz hyw hneIn hneOut
            exact hthird (htailEdges _ hxy) (htailEdges _ hyz)
              hxz hyw hneIn hneOut
          have hnext : ∃ k ∈ flankFaces c d,
              k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
            by_cases had : a = d
            · subst d
              exact ⟨h, by simpa [flankFaces_comm] using hh, hhRegion⟩
            · apply rlc_centralFaceRegion_continue_consecutive_wall_flank
                gamma gamma' hac hcd had
                  (hqInterior c (by simp))
              · intro w hcw hneIn hneOut
                exact hthird hacEdge hcdEdge had hcw hneIn hneOut
              · exact hhRegion
              · exact hh
          obtain ⟨k, hkFlank, hkRegion⟩ := hnext
          exact ih (h := k) (by simp) htailInterior htailThird
            hkRegion (by simpa using hkFlank)


theorem rlc_positive_reflectedLeft_walk_terminal_regionFlank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {b u : Site 2}
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk b u)
    (hrPos : ∀ x ∈ r.support, 0 < (rlc_dualReflect x) 0)
    (hrNoRight : ∀ x ∈ r.support,
      rlc_dualReflect x ∉ rlc_pathVertices gamma.1)
    (hrLeft : ∀ {f g : Site 2}, s(f, g) ∈ r.edges →
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_reflectedPathEdges gamma'.1)
    (hrNotNil : ¬ r.Nil)
    (hrInterior : ∀ x ∈ r.support,
      -2 * n < (rlc_dualReflect x) 0 ∧
        (rlc_dualReflect x) 0 < 2 * n ∧
        -n < (rlc_dualReflect x) 1 ∧
        (rlc_dualReflect x) 1 < n)
    {h : Site 2}
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect b)
      (rlc_dualReflect r.snd)) :
    ∃ k ∈ flankFaces (rlc_dualReflect r.penultimate)
        (rlc_dualReflect u),
      k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  let hDual :
      rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho →g
        hypercubicLattice 2 := {
    toFun := rlc_dualReflect
    map_rel' := fun {f g} hfg => (rlc_adj_dualReflect f g).mp hfg.1.1
  }
  let rDual : (hypercubicLattice 2).Walk
      (rlc_dualReflect b) (rlc_dualReflect u) := r.map hDual
  have hrDualNotNil : ¬ rDual.Nil := by
    simpa [rDual] using hrNotNil
  have hrDualInterior : ∀ y ∈ rDual.support,
      -2 * n < y 0 ∧ y 0 < 2 * n ∧ -n < y 1 ∧ y 1 < n := by
    intro y hy
    change y ∈ (r.map hDual).support at hy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hrInterior x hx
  have hrDualPos {y : Site 2} (hy : y ∈ rDual.support) : 0 < y 0 := by
    change y ∈ (r.map hDual).support at hy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hrPos x hx
  have hrDualNoRight {y : Site 2} (hy : y ∈ rDual.support) :
      y ∉ rlc_pathVertices gamma.1 := by
    change y ∈ (r.map hDual).support at hy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hrNoRight x hx
  have hrDualLeft {e : Sym2 (Site 2)} (he : e ∈ rDual.edges) :
      e ∈ rlc_reflectedPathEdges gamma'.1 := by
    change e ∈ (r.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    induction e0 using Sym2.inductionOn with
    | _ f g => exact hrLeft he0
  have hrDualThird : ∀ {x y z w : Site 2},
      s(x, y) ∈ rDual.edges → s(y, z) ∈ rDual.edges → x ≠ z →
      (hypercubicLattice 2).Adj y w →
      s(y, w) ≠ s(x, y) → s(y, w) ≠ s(y, z) →
      s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
    intro x y z w hxy hyz hxz hyw hneIn hneOut
    have hySupport := rDual.snd_mem_support_of_mem_edges hxy
    exact rlc_positive_reflectedLeft_third_incident_nonwall
      gamma gamma' (hrDualPos hySupport) (hrDualNoRight hySupport)
        (hrDualLeft hxy) (hrDualLeft hyz) hxz hneIn hneOut
  have hout := rlc_walk_terminal_regionFlank_of_consecutive_detours
    gamma gamma' rDual hrDualNotNil hrDualInterior hrDualThird
      hhRegion (by simpa [rDual] using hh)
  simpa [rDual] using hout


theorem rlc_negative_reflectedRight_walk_terminal_regionFlank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {b u : Site 2}
    (r : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk b u)
    (hrNeg : ∀ x ∈ r.support, (rlc_dualReflect x) 0 < 0)
    (hrNoLeft : ∀ x ∈ r.support,
      rlc_dualReflect x ∉ rlc_pathVertices gamma'.1)
    (hrRight : ∀ {f g : Site 2}, s(f, g) ∈ r.edges →
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_reflectedPathEdges gamma.1)
    (hrNotNil : ¬ r.Nil)
    (hrInterior : ∀ x ∈ r.support,
      -2 * n < (rlc_dualReflect x) 0 ∧
        (rlc_dualReflect x) 0 < 2 * n ∧
        -n < (rlc_dualReflect x) 1 ∧
        (rlc_dualReflect x) 1 < n)
    {h : Site 2}
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces (rlc_dualReflect b)
      (rlc_dualReflect r.snd)) :
    ∃ k ∈ flankFaces (rlc_dualReflect r.penultimate)
        (rlc_dualReflect u),
      k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  let hDual :
      rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho →g
        hypercubicLattice 2 := {
    toFun := rlc_dualReflect
    map_rel' := fun {f g} hfg => (rlc_adj_dualReflect f g).mp hfg.1.1
  }
  let rDual : (hypercubicLattice 2).Walk
      (rlc_dualReflect b) (rlc_dualReflect u) := r.map hDual
  have hrDualNotNil : ¬ rDual.Nil := by
    simpa [rDual] using hrNotNil
  have hrDualInterior : ∀ y ∈ rDual.support,
      -2 * n < y 0 ∧ y 0 < 2 * n ∧ -n < y 1 ∧ y 1 < n := by
    intro y hy
    change y ∈ (r.map hDual).support at hy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hrInterior x hx
  have hrDualNeg {y : Site 2} (hy : y ∈ rDual.support) : y 0 < 0 := by
    change y ∈ (r.map hDual).support at hy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hrNeg x hx
  have hrDualNoLeft {y : Site 2} (hy : y ∈ rDual.support) :
      y ∉ rlc_pathVertices gamma'.1 := by
    change y ∈ (r.map hDual).support at hy
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hrNoLeft x hx
  have hrDualRight {e : Sym2 (Site 2)} (he : e ∈ rDual.edges) :
      e ∈ rlc_reflectedPathEdges gamma.1 := by
    change e ∈ (r.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    induction e0 using Sym2.inductionOn with
    | _ f g => exact hrRight he0
  have hrDualThird : ∀ {x y z w : Site 2},
      s(x, y) ∈ rDual.edges → s(y, z) ∈ rDual.edges → x ≠ z →
      (hypercubicLattice 2).Adj y w →
      s(y, w) ≠ s(x, y) → s(y, w) ≠ s(y, z) →
      s(y, w) ∉ rlc_connectorFourTraceEdges gamma gamma' := by
    intro x y z w hxy hyz hxz hyw hneIn hneOut
    have hySupport := rDual.snd_mem_support_of_mem_edges hxy
    exact rlc_negative_reflectedRight_third_incident_nonwall
      gamma gamma' (hrDualNeg hySupport) (hrDualNoLeft hySupport)
        (hrDualRight hxy) (hrDualRight hyz) hxz hneIn hneOut
  have hout := rlc_walk_terminal_regionFlank_of_consecutive_detours
    gamma gamma' rDual hrDualNotNil hrDualInterior hrDualThird
      hhRegion (by simpa [rDual] using hh)
  simpa [rDual] using hout


theorem rlc_centralFaceRegion_first_wall_flank_of_nonwall_entry
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    {a b c d h : Site 2}
    (hba : (hypercubicLattice 2).Adj b a)
    (hbc : (hypercubicLattice 2).Adj b c)
    (hbd : (hypercubicLattice 2).Adj b d)
    (hac : a ≠ c) (hdc : d ≠ c)
    (hentryNot : s(a, b) ∉ rlc_connectorFourTraceEdges gamma gamma')
    (hbdWall : s(b, d) ∈ rlc_connectorFourTraceEdges gamma gamma')
    (hbInterior : -2 * n < b 0 ∧ b 0 < 2 * n ∧
      -n < b 1 ∧ b 1 < n)
    (hother : ∀ w : Site 2,
      (hypercubicLattice 2).Adj b w →
      s(b, w) ≠ s(d, b) → s(b, w) ≠ s(b, c) →
      s(b, w) ∉ rlc_connectorFourTraceEdges gamma gamma')
    (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
    (hh : h ∈ flankFaces a b) :
    ∃ k ∈ flankFaces b c,
      k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
  have hentryNot' : s(b, a) ∉
      rlc_connectorFourTraceEdges gamma gamma' := by
    simpa [Sym2.eq_swap] using hentryNot
  have hh' : h ∈ flankFaces b a := by
    simpa [flankFaces_comm] using hh
  have entryRegion {k : Site 2} (hk : k ∈ flankFaces b a) :
      k ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
    have hkBox := rlc_flank_mem_connectorFaceBox_of_interior
      hba hbInterior hk
    exact rlc_centralFaceRegion_other_flank_of_nonwall
      gamma gamma' hba hentryNot' hhRegion hh' hk hkBox
  by_cases hoppAC : a 0 + c 0 = 2 * b 0 ∧
      a 1 + c 1 = 2 * b 1
  · have had : a ≠ d := by
      intro had
      subst d
      exact hentryNot' hbdWall
    have hnoppAD : ¬ (a 0 + d 0 = 2 * b 0 ∧
        a 1 + d 1 = 2 * b 1) := by
      intro hoppAD
      apply hdc
      have h0 : d 0 = c 0 := by omega
      have h1 : d 1 = c 1 := by omega
      funext i
      fin_cases i
      · exact h0
      · exact h1
    obtain ⟨k, hkEntry, hkSecond⟩ :=
      rlc_incident_flank_intersection_of_not_opposite
        hba hbd had hnoppAD
    have hkRegion := entryRegion hkEntry
    exact rlc_centralFaceRegion_continue_consecutive_wall_flank
      gamma gamma' hbd.symm hbc hdc hbInterior hother
        hkRegion (by simpa [flankFaces_comm] using hkSecond)
  · obtain ⟨k, hkEntry, hkOut⟩ :=
      rlc_incident_flank_intersection_of_not_opposite
        hba hbc hac hoppAC
    exact ⟨k, hkOut, entryRegion hkEntry⟩


theorem rlc_positiveStrictWallEntryDecomp_boundary_or_terminalRegionFlank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hentry : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        ((rlc_dualReflect x) 0 = -2 * n ∨
          (rlc_dualReflect x) 0 = 2 * n ∨
          (rlc_dualReflect x) 1 = -n ∨
          (rlc_dualReflect x) 1 = n)) ∨
      ∃ (t h : Site 2),
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Adj t u ∧
        s(rlc_dualReflect t, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma'.1 ∧
        h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
        h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) := by
  obtain ⟨A, a, b, pA, p, r, hanchor, hab, hdecomp, hAzero,
    hAstart, hentryNot, hrPos, hrNoRight, hrLeft, hrNotNil⟩ := hentry
  have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace A := ⟨pA.reverse⟩
  have reach_of_mem_r (x : Site 2) (hx : x ∈ r.support) :
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        L.boundary.firstFace x :=
    hfirstA.trans ⟨p.append (.cons hab (r.takeUntil x hx))⟩
  by_cases hrInterior : ∀ x ∈ r.support,
      -2 * n < (rlc_dualReflect x) 0 ∧
        (rlc_dualReflect x) 0 < 2 * n ∧
        -n < (rlc_dualReflect x) 1 ∧
        (rlc_dualReflect x) 1 < n
  · right
    let c := r.snd
    have hbcSource : s(b, c) ∈ r.edges := by
      exact r.mk_start_snd_mem_edges hrNotNil
    have hbcLeft : s(rlc_dualReflect b, rlc_dualReflect c) ∈
        rlc_reflectedPathEdges gamma'.1 := hrLeft hbcSource
    have hbcWall : s(rlc_dualReflect b, rlc_dualReflect c) ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
      rw [rlc_connectorFourTraceEdges, rlc_connectorReflectedTraceEdges]
      exact Finset.mem_union_right _ (Finset.mem_union_right _ hbcLeft)
    let W := (rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom
    have hbcW : s(rlc_dualReflect b, rlc_dualReflect c) ∈ W.edges :=
      rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
        gamma'.1 hbcLeft
    have hbStart : rlc_dualReflect b ≠
        rlc_flipX (gamma'.1.1 : Site 2) := by
      intro heq
      have hbInt := hrInterior b r.start_mem_support
      have h0 := congrArg (fun z : Site 2 => z 0) heq
      change (rlc_dualReflect b) 0 =
        -(gamma'.1.1 : Site 2) 0 at h0
      have hs : (gamma'.1.1 : Site 2) 0 = -2 * n :=
        gamma'.1.1.2.2
      omega
    have hbFinish : rlc_dualReflect b ≠
        rlc_flipX (gamma'.1.2.1 : Site 2) := by
      intro heq
      have hbPos := hrPos b r.start_mem_support
      have h0 := congrArg (fun z : Site 2 => z 0) heq
      change (rlc_dualReflect b) 0 =
        -(gamma'.1.2.1 : Site 2) 0 at h0
      have hs : (gamma'.1.2.1 : Site 2) 0 = 0 :=
        gamma'.1.2.1.2.2
      omega
    obtain ⟨d, hbdW, hdc⟩ := rlc_isPath_exists_other_incident_edge
      W (rlc_reflectedAmbientCrossingWalk_isPath gamma'.1)
        hbcW hbStart hbFinish
    have hbdLeft : s(rlc_dualReflect b, d) ∈
        rlc_reflectedPathEdges gamma'.1 := by
      change s(rlc_dualReflect b, d) ∈
        ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).edges at hbdW
      rw [SimpleGraph.Walk.edges_map, List.mem_map] at hbdW
      obtain ⟨e0, he0, heq⟩ := hbdW
      rw [rlc_reflectedPathEdges, Finset.mem_image]
      exact ⟨e0, rlc_ambientCrossingWalk_edge_mem_pathEdges
        gamma'.1 he0, heq⟩
    have hbdWall : s(rlc_dualReflect b, d) ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
      rw [rlc_connectorFourTraceEdges, rlc_connectorReflectedTraceEdges]
      exact Finset.mem_union_right _ (Finset.mem_union_right _ hbdLeft)
    have hac : rlc_dualReflect a ≠ rlc_dualReflect c := by
      intro hac
      apply hentryNot
      simpa [hac, Sym2.eq_swap] using hbcWall
    have hbAdjC : (hypercubicLattice 2).Adj
        (rlc_dualReflect b) (rlc_dualReflect c) :=
      (rlc_adj_dualReflect b c).mp (r.adj_snd hrNotNil).1.1
    have hbAdjD : (hypercubicLattice 2).Adj (rlc_dualReflect b) d :=
      W.adj_of_mem_edges hbdW
    have hbNoRight := hrNoRight b r.start_mem_support
    have hother : ∀ w : Site 2,
        (hypercubicLattice 2).Adj (rlc_dualReflect b) w →
        s(rlc_dualReflect b, w) ≠ s(d, rlc_dualReflect b) →
        s(rlc_dualReflect b, w) ≠
          s(rlc_dualReflect b, rlc_dualReflect c) →
        s(rlc_dualReflect b, w) ∉
          rlc_connectorFourTraceEdges gamma gamma' := by
      intro w hbw hneD hneC
      exact rlc_positive_reflectedLeft_third_incident_nonwall
        gamma gamma' (hrPos b r.start_mem_support) hbNoRight
          (by simpa [Sym2.eq_swap] using hbdLeft) hbcLeft hdc hneD hneC
    have hregion : ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
        h ∈ flankFaces (rlc_dualReflect a) (rlc_dualReflect b) := by
      rcases hab.2 with hwall | hregion
      · exact False.elim (hentryNot hwall)
      · exact hregion.2.2
    obtain ⟨h0, hh0Region, hh0⟩ := hregion
    obtain ⟨k, hkFirst, hkRegion⟩ :=
      rlc_centralFaceRegion_first_wall_flank_of_nonwall_entry
        gamma gamma'
          ((rlc_adj_dualReflect b a).mp hab.1.1.symm)
          hbAdjC hbAdjD hac hdc hentryNot hbdWall
          (hrInterior b r.start_mem_support) hother hh0Region hh0
    obtain ⟨k', hk'Flank, hk'Region⟩ :=
      rlc_positive_reflectedLeft_walk_terminal_regionFlank
        r hrPos hrNoRight hrLeft hrNotNil hrInterior hkRegion
          (by simpa [c] using hkFirst)
    refine ⟨r.penultimate, k', r.adj_penultimate hrNotNil, ?_,
      hk'Region, hk'Flank⟩
    exact hrLeft (r.mk_penultimate_end_mem_edges hrNotNil)
  · push Not at hrInterior
    obtain ⟨x, hx, hxNotInterior⟩ := hrInterior
    left
    have hxReach := reach_of_mem_r x hx
    have hxBox := rlc_goodBoundary_reachable_dualReflect_mem_box
      L.boundary hfaith hxReach
    refine ⟨x, hxReach, ?_⟩
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at hxBox
    rw [mem_rect] at hxBox
    omega


theorem rlc_negativeStrictWallEntryDecomp_boundary_or_terminalRegionFlank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hentry : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        ((rlc_dualReflect x) 0 = -2 * n ∨
          (rlc_dualReflect x) 0 = 2 * n ∨
          (rlc_dualReflect x) 1 = -n ∨
          (rlc_dualReflect x) 1 = n)) ∨
      ∃ (t h : Site 2),
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Adj t u ∧
        s(rlc_dualReflect t, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma.1 ∧
        h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
        h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) := by
  obtain ⟨A, a, b, pA, p, r, hab, hdecomp, hAzero, hAoff,
    hentryNot, hrNeg, hrNoLeft, hrRight, hrNotNil⟩ := hentry
  have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace A := ⟨pA.reverse⟩
  have reach_of_mem_r (x : Site 2) (hx : x ∈ r.support) :
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
        L.boundary.firstFace x :=
    hfirstA.trans ⟨p.append (.cons hab (r.takeUntil x hx))⟩
  by_cases hrInterior : ∀ x ∈ r.support,
      -2 * n < (rlc_dualReflect x) 0 ∧
        (rlc_dualReflect x) 0 < 2 * n ∧
        -n < (rlc_dualReflect x) 1 ∧
        (rlc_dualReflect x) 1 < n
  · right
    let c := r.snd
    have hbcSource : s(b, c) ∈ r.edges := r.mk_start_snd_mem_edges hrNotNil
    have hbcRight : s(rlc_dualReflect b, rlc_dualReflect c) ∈
        rlc_reflectedPathEdges gamma.1 := hrRight hbcSource
    have hbcWall : s(rlc_dualReflect b, rlc_dualReflect c) ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
      rw [rlc_connectorFourTraceEdges, rlc_connectorReflectedTraceEdges]
      exact Finset.mem_union_right _ (Finset.mem_union_left _ hbcRight)
    let W := ((rlc_ambientCrossingWalk gamma.1).map
      rlc_flipXLatticeHom).reverse
    have hbcW : s(rlc_dualReflect b, rlc_dualReflect c) ∈ W.edges := by
      have hf :=
        rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
          gamma.1 hbcRight
      simpa [W, SimpleGraph.Walk.edges_reverse] using hf
    have hbStart : rlc_dualReflect b ≠
        rlc_flipX (gamma.1.2.1 : Site 2) := by
      intro heq
      have hbInt := hrInterior b r.start_mem_support
      have h0 := congrArg (fun z : Site 2 => z 0) heq
      change (rlc_dualReflect b) 0 = -(gamma.1.2.1 : Site 2) 0 at h0
      have hs : (gamma.1.2.1 : Site 2) 0 = 2 * n :=
        gamma.1.2.1.2.2
      omega
    have hbFinish : rlc_dualReflect b ≠
        rlc_flipX (gamma.1.1 : Site 2) := by
      intro heq
      have hbNeg := hrNeg b r.start_mem_support
      have h0 := congrArg (fun z : Site 2 => z 0) heq
      change (rlc_dualReflect b) 0 = -(gamma.1.1 : Site 2) 0 at h0
      have hs : (gamma.1.1 : Site 2) 0 = 0 := gamma.1.1.2.2
      omega
    obtain ⟨d, hbdW, hdc⟩ := rlc_isPath_exists_other_incident_edge
      W (rlc_reflectedAmbientCrossingWalk_isPath gamma.1).reverse
        hbcW hbStart hbFinish
    have hbdRight : s(rlc_dualReflect b, d) ∈
        rlc_reflectedPathEdges gamma.1 := by
      have hbdForward : s(rlc_dualReflect b, d) ∈
          ((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).edges := by
        simpa [W, SimpleGraph.Walk.edges_reverse] using hbdW
      rw [SimpleGraph.Walk.edges_map, List.mem_map] at hbdForward
      obtain ⟨e0, he0, heq⟩ := hbdForward
      rw [rlc_reflectedPathEdges, Finset.mem_image]
      exact ⟨e0, rlc_ambientCrossingWalk_edge_mem_pathEdges
        gamma.1 he0, heq⟩
    have hbdWall : s(rlc_dualReflect b, d) ∈
        rlc_connectorFourTraceEdges gamma gamma' := by
      rw [rlc_connectorFourTraceEdges, rlc_connectorReflectedTraceEdges]
      exact Finset.mem_union_right _ (Finset.mem_union_left _ hbdRight)
    have hac : rlc_dualReflect a ≠ rlc_dualReflect c := by
      intro hac
      apply hentryNot
      simpa [hac, Sym2.eq_swap] using hbcWall
    have hbAdjC : (hypercubicLattice 2).Adj
        (rlc_dualReflect b) (rlc_dualReflect c) :=
      (rlc_adj_dualReflect b c).mp (r.adj_snd hrNotNil).1.1
    have hbAdjD : (hypercubicLattice 2).Adj (rlc_dualReflect b) d :=
      W.adj_of_mem_edges hbdW
    have hbNoLeft := hrNoLeft b r.start_mem_support
    have hother : ∀ w : Site 2,
        (hypercubicLattice 2).Adj (rlc_dualReflect b) w →
        s(rlc_dualReflect b, w) ≠ s(d, rlc_dualReflect b) →
        s(rlc_dualReflect b, w) ≠
          s(rlc_dualReflect b, rlc_dualReflect c) →
        s(rlc_dualReflect b, w) ∉
          rlc_connectorFourTraceEdges gamma gamma' := by
      intro w hbw hneD hneC
      exact rlc_negative_reflectedRight_third_incident_nonwall
        gamma gamma' (hrNeg b r.start_mem_support) hbNoLeft
          (by simpa [Sym2.eq_swap] using hbdRight) hbcRight hdc hneD hneC
    have hregion : ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
        h ∈ flankFaces (rlc_dualReflect a) (rlc_dualReflect b) := by
      rcases hab.2 with hwall | hregion
      · exact False.elim (hentryNot hwall)
      · exact hregion.2.2
    obtain ⟨h0, hh0Region, hh0⟩ := hregion
    obtain ⟨k, hkFirst, hkRegion⟩ :=
      rlc_centralFaceRegion_first_wall_flank_of_nonwall_entry
        gamma gamma' ((rlc_adj_dualReflect b a).mp hab.1.1.symm)
          hbAdjC hbAdjD hac hdc hentryNot hbdWall
          (hrInterior b r.start_mem_support) hother hh0Region hh0
    obtain ⟨k', hk'Flank, hk'Region⟩ :=
      rlc_negative_reflectedRight_walk_terminal_regionFlank
        r hrNeg hrNoLeft hrRight hrNotNil hrInterior hkRegion
          (by simpa [c] using hkFirst)
    refine ⟨r.penultimate, k', r.adj_penultimate hrNotNil, ?_,
      hk'Region, hk'Flank⟩
    exact hrRight (r.mk_penultimate_end_mem_edges hrNotNil)
  · push Not at hrInterior
    obtain ⟨x, hx, hxNotInterior⟩ := hrInterior
    left
    have hxReach := reach_of_mem_r x hx
    have hxBox := rlc_goodBoundary_reachable_dualReflect_mem_box
      L.boundary hfaith hxReach
    refine ⟨x, hxReach, ?_⟩
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at hxBox
    rw [mem_rect] at hxBox
    omega


theorem rlc_positiveStrictWallEntryDecomp_boundary_or_terminalSideChange
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u v : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hentry : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        ((rlc_dualReflect x) 0 = -2 * n ∨
          (rlc_dualReflect x) 0 = 2 * n ∨
          (rlc_dualReflect x) 1 = -n ∨
          (rlc_dualReflect x) 1 = n)) ∨
      ∃ (t h : Site 2),
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Adj t u ∧
        s(rlc_dualReflect t, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma'.1 ∧
        h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
        h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) ∧
        s(rlc_dualReflect u, rlc_dualReflect v) ∉
          rlc_connectorFourTraceEdges gamma gamma' ∧
        rlc_dualReflect u ∈ rlc_connectorBox n ∧
        rlc_dualReflect v ∈ rlc_connectorBox n ∧
        ∀ k ∈ rlc_connectorCentralFaceRegion gamma gamma',
          k ∉ flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
  have hentry' := hentry
  obtain ⟨A, a, b, pA, p, r, hanchor, hab, hdecomp, hAzero,
    hAstart, hentryNot, hrPos, hrNoRight, hrLeft, hrNotNil⟩ := hentry
  rcases rlc_positiveStrictWallEntryDecomp_boundary_or_terminalRegionFlank
      hfaith hentry' with hboundary | ⟨t, h, htu, htuLeft,
        hhRegion, hhFlank⟩
  · exact Or.inl hboundary
  · by_cases hrInterior : ∀ x ∈ r.support,
        -2 * n < (rlc_dualReflect x) 0 ∧
          (rlc_dualReflect x) 0 < 2 * n ∧
          -n < (rlc_dualReflect x) 1 ∧
          (rlc_dualReflect x) 1 < n
    · have hout := rlc_badExit_interior_nonwall_box_noCentralFlank
          huv (hrInterior u r.end_mem_support) hbad
      exact Or.inr ⟨t, h, htu, htuLeft, hhRegion, hhFlank,
        hout.1, hout.2.1, hout.2.2.1, hout.2.2.2⟩
    · push Not at hrInterior
      obtain ⟨x, hx, hxNotInterior⟩ := hrInterior
      have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable L.boundary.firstFace A := ⟨pA.reverse⟩
      have hxReach : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable L.boundary.firstFace x :=
        hfirstA.trans ⟨p.append (.cons hab (r.takeUntil x hx))⟩
      have hxBox := rlc_goodBoundary_reachable_dualReflect_mem_box
        L.boundary hfaith hxReach
      left
      refine ⟨x, hxReach, ?_⟩
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at hxBox
      rw [mem_rect] at hxBox
      omega


theorem rlc_negativeStrictWallEntryDecomp_boundary_or_terminalSideChange
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u v : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hentry : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        ((rlc_dualReflect x) 0 = -2 * n ∨
          (rlc_dualReflect x) 0 = 2 * n ∨
          (rlc_dualReflect x) 1 = -n ∨
          (rlc_dualReflect x) 1 = n)) ∨
      ∃ (t h : Site 2),
        (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Adj t u ∧
        s(rlc_dualReflect t, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma.1 ∧
        h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
        h ∈ flankFaces (rlc_dualReflect t) (rlc_dualReflect u) ∧
        s(rlc_dualReflect u, rlc_dualReflect v) ∉
          rlc_connectorFourTraceEdges gamma gamma' ∧
        rlc_dualReflect u ∈ rlc_connectorBox n ∧
        rlc_dualReflect v ∈ rlc_connectorBox n ∧
        ∀ k ∈ rlc_connectorCentralFaceRegion gamma gamma',
          k ∉ flankFaces (rlc_dualReflect u) (rlc_dualReflect v) := by
  have hentry' := hentry
  obtain ⟨A, a, b, pA, p, r, hab, hdecomp, hAzero, hAoff,
    hentryNot, hrNeg, hrNoLeft, hrRight, hrNotNil⟩ := hentry
  rcases rlc_negativeStrictWallEntryDecomp_boundary_or_terminalRegionFlank
      hfaith hentry' with hboundary | ⟨t, h, htu, htuRight,
        hhRegion, hhFlank⟩
  · exact Or.inl hboundary
  · by_cases hrInterior : ∀ x ∈ r.support,
        -2 * n < (rlc_dualReflect x) 0 ∧
          (rlc_dualReflect x) 0 < 2 * n ∧
          -n < (rlc_dualReflect x) 1 ∧
          (rlc_dualReflect x) 1 < n
    · have hout := rlc_badExit_interior_nonwall_box_noCentralFlank
          huv (hrInterior u r.end_mem_support) hbad
      exact Or.inr ⟨t, h, htu, htuRight, hhRegion, hhFlank,
        hout.1, hout.2.1, hout.2.2.1, hout.2.2.2⟩
    · push Not at hrInterior
      obtain ⟨x, hx, hxNotInterior⟩ := hrInterior
      have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable L.boundary.firstFace A := ⟨pA.reverse⟩
      have hxReach : (rlc_connectorCentralFaceGoodBoundaryGraph
          gamma gamma' rho).Reachable L.boundary.firstFace x :=
        hfirstA.trans ⟨p.append (.cons hab (r.takeUntil x hx))⟩
      have hxBox := rlc_goodBoundary_reachable_dualReflect_mem_box
        L.boundary hfaith hxReach
      left
      refine ⟨x, hxReach, ?_⟩
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at hxBox
      rw [mem_rect] at hxBox
      omega


end
end StatMech.Universality
