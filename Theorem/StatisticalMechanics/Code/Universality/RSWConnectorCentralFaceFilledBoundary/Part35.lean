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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part31
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRun_reachableRight_or_axisSuffix_or_strictEntry
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hrun : RlcCentralFacePositiveWallRunSurgeryAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      RlcCentralFacePositiveReflectedLeftAxisSuffixAt
        gamma gamma' rho u ∨
      RlcCentralFacePositiveStrictWallEntryAt gamma gamma' rho L u := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAstart, hentry,
    hrWall, hrNotNil, w, hw, huw⟩ := hrun
  obtain ⟨A0, hfirstA0, _hA0first, hA0zero, _hA0class⟩ :=
    rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier
      L.boundary hfaith
  have hA0A : A0 = A := by
    apply rlc_dualReflect.injective
    exact hA0zero.trans hAzero.symm
  have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace A := by
    simpa [hA0A] using hfirstA0
  have reach_of_mem_r (x : Site 2) (hx : x ∈ r.support) :
      (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable L.boundary.firstFace x := by
    exact hfirstA.trans ⟨p.append (.cons hab (r.takeUntil x hx))⟩
  by_cases hright : ∃ x ∈ r.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1
  · left
    obtain ⟨x, hx, hxRight⟩ := hright
    exact ⟨x, reach_of_mem_r x hx, hxRight⟩
  · push Not at hright
    rcases rlc_walk_all_positive_or_last_nonpositive_decomp
        (fun x => (rlc_dualReflect x) 0) r huPos with
      hallPos | ⟨c, d, pr, s, hcd, hcNonpos, hdPos,
        hsPos, hrDecomp⟩
    · right; right
      refine ⟨A, a, b, p, r, hab, hAzero, hAstart, hentry,
        hallPos, hright, ?_, hrNotNil⟩
      intro f g hfg
      exact rlc_nonnegative_wallPath_edge_reflectedLeft
        hfaith r hrWall hright
          (fun x hx => le_of_lt (hallPos x hx)) hfg
    · have hcdR : s(c, d) ∈ r.edges := by
        rw [hrDecomp, SimpleGraph.Walk.edges_append]
        simp
      have hcdWall : s(rlc_dualReflect c, rlc_dualReflect d) ∈
          rlc_connectorFourTraceEdges gamma gamma' := by
        simpa [Sym2.map_mk] using hrWall _ hcdR
      have hcdTarget : (hypercubicLattice 2).Adj
          (rlc_dualReflect c) (rlc_dualReflect d) :=
        (rlc_adj_dualReflect c d).mp hcd.1.1
      have hcZero : (rlc_dualReflect c) 0 = 0 := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two] at hcdTarget
        omega
      have hcBarrier : rlc_dualReflect c ∈
          rlc_connectorBarrier gamma gamma' :=
        rlc_mem_connectorBarrier_of_mem_fourTraceEdge
          gamma gamma' hcdWall (Sym2.mem_mk_left _ _)
      have hcEq : rlc_dualReflect c =
          (![0, (rlc_dualReflect c) 1] : Site 2) := by
        ext i
        fin_cases i <;> simp [hcZero]
      rcases (rlc_axis_mem_connectorBarrier_iff gamma gamma'
          ((rlc_dualReflect c) 1)).1 (by
            rwa [← hcEq]) with hcRight | hcLeft
      · left
        have hcR : c ∈ r.support := by
          rw [hrDecomp, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr (SimpleGraph.Walk.cons hcd s).start_mem_support
        exact ⟨c, reach_of_mem_r c hcR, by
          rwa [hcEq]⟩
      · right; left
        let q : (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Walk c u := .cons hcd s
        have hqSupport : ∀ x ∈ q.support, x ∈ r.support := by
          intro x hx
          rw [hrDecomp, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr hx
        have hqNoRight : ∀ x ∈ q.support,
            rlc_dualReflect x ∉ rlc_pathVertices gamma.1 := by
          intro x hx
          exact hright x (hqSupport x hx)
        have hqWall : ∀ e ∈ q.edges,
            Sym2.map rlc_dualReflect e ∈
              rlc_connectorFourTraceEdges gamma gamma' := by
          intro e he
          apply hrWall e
          rw [hrDecomp, SimpleGraph.Walk.edges_append, List.mem_append]
          exact Or.inr he
        have hqNonneg : ∀ x ∈ q.support,
            0 ≤ (rlc_dualReflect x) 0 := by
          intro x hx
          simp only [q, SimpleGraph.Walk.support_cons,
            List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact le_of_eq hcZero.symm
          · exact le_of_lt (hsPos x hx)
        have hcLeft' : rlc_dualReflect c ∈
            rlc_pathVertices gamma'.1 := by
          rwa [hcEq]
        have hcEnd := hfaith.left_axis_unique hcLeft' hcZero
        refine ⟨c, q, hcEnd, hqNoRight, ?_⟩
        intro f g hfg
        exact rlc_nonnegative_wallPath_edge_reflectedLeft
          hfaith q hqWall hqNoRight hqNonneg hfg


theorem rlc_reflectedLeftAxisWalk_end_mem_firstIntersectionSuffix
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {c u : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk c u)
    (hcEnd : rlc_dualReflect c = (gamma'.1.2.1 : Site 2))
    (hqNoRight : ∀ x ∈ q.support,
      rlc_dualReflect x ∉ rlc_pathVertices gamma.1)
    (hqReflectedLeft : ∀ {f g : Site 2}, s(f, g) ∈ q.edges →
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_reflectedPathEdges gamma'.1) :
    ∃ (z : Site 2)
      (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect u ∈
          (((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).dropUntil z hz).support := by
  obtain ⟨z, _hzWR, hzRight, hzLeft, _hfirst, _hglobalMin⟩ :=
    rlc_bookFirstFlippedTraceIntersection_of_faithful
      gamma gamma' hfaith
  let W := (rlc_ambientCrossingWalk gamma'.1).map
    rlc_flipXLatticeHom
  have hflipZWL : rlc_flipX z ∈
      (rlc_ambientCrossingWalk gamma'.1).support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX z)).2 hzLeft
  have hzW : z ∈ W.support := by
    change z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
      rlc_flipXLatticeHom).support
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨rlc_flipX z, hflipZWL, rlc_flipX_involutive z⟩
  let hDual :
      rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho →g
        hypercubicLattice 2 := {
    toFun := rlc_dualReflect
    map_rel' := fun {f g} hfg =>
      (rlc_adj_dualReflect f g).mp hfg.1.1
  }
  let qDual : (hypercubicLattice 2).Walk
      (rlc_dualReflect c) (rlc_dualReflect u) := q.map hDual
  have hqDualEdges : ∀ e ∈ qDual.edges, e ∈ W.edges := by
    intro e he
    change e ∈ (q.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    induction e0 using Sym2.inductionOn with
    | _ f g =>
        apply rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
          gamma'.1
        exact hqReflectedLeft he0
  have hqDualAvoid : z ∉ qDual.support := by
    intro hzq
    change z ∈ (q.map hDual).support at hzq
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzq
    obtain ⟨x, hxQ, hxz⟩ := hzq
    change rlc_dualReflect x = z at hxz
    exact hqNoRight x hxQ (by simpa [hxz] using hzRight)
  have hupperFlip : rlc_flipX (gamma'.1.2.1 : Site 2) =
      (gamma'.1.2.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma'.1.2.1.2.2
  have hcInSuffix : rlc_dualReflect c ∈
      (W.dropUntil z hzW).support := by
    rw [hcEnd]
    have hend : rlc_flipX (gamma'.1.2.1 : Site 2) ∈
        (W.dropUntil z hzW).support :=
      (W.dropUntil z hzW).end_mem_support
    rw [hupperFlip] at hend
    exact hend
  have huSuffix := rlc_walk_end_mem_pathSuffix_of_avoid
    W (rlc_reflectedAmbientCrossingWalk_isPath gamma'.1)
      hzW qDual hcInSuffix hqDualEdges hqDualAvoid
  exact ⟨z, hzW, hzRight, hzLeft, huSuffix⟩


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRun_reachableRight_or_firstIntersectionSuffix_or_strictEntry
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hrun : RlcCentralFacePositiveWallRunSurgeryAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      (∃ (z : Site 2)
        (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
          rlc_flipXLatticeHom).support),
        z ∈ rlc_pathVertices gamma.1 ∧
          rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
          rlc_dualReflect u ∈
            (((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).dropUntil z hz).support) ∨
      RlcCentralFacePositiveStrictWallEntryAt gamma gamma' rho L u := by
  rcases L.positiveWallRun_reachableRight_or_axisSuffix_or_strictEntry
      hfaith hrun huPos with hright | haxis | hstrict
  · exact Or.inl hright
  · right; left
    obtain ⟨c, q, hcEnd, hqNoRight, hqLeft⟩ := haxis
    exact rlc_reflectedLeftAxisWalk_end_mem_firstIntersectionSuffix
      hfaith q hcEnd hqNoRight hqLeft
  · exact Or.inr (Or.inr hstrict)


theorem rlc_nonpositive_wallPath_edge_reflectedRight
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {A u : Site 2}
    (p : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk A u)
    (hpWall : ∀ e ∈ p.edges,
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma')
    (hpNoLeft : ∀ z ∈ p.support,
      rlc_dualReflect z ∉ rlc_pathVertices gamma'.1)
    (hpNonpos : ∀ z ∈ p.support, (rlc_dualReflect z) 0 ≤ 0)
    {f g : Site 2} (hfg : s(f, g) ∈ p.edges) :
    s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_reflectedPathEdges gamma.1 := by
  have hfP := p.fst_mem_support_of_mem_edges hfg
  have hgP := p.snd_mem_support_of_mem_edges hfg
  have hfNonpos := hpNonpos f hfP
  have hgNonpos := hpNonpos g hgP
  have hfgWall : s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_connectorFourTraceEdges gamma gamma' := by
    simpa [Sym2.map_mk] using hpWall _ hfg
  have hfgAdj : (hypercubicLattice 2).Adj
      (rlc_dualReflect f) (rlc_dualReflect g) :=
    (rlc_adj_dualReflect f g).mp (p.adj_of_mem_edges hfg).1.1
  have hsomeNeg : (rlc_dualReflect f) 0 < 0 ∨
      (rlc_dualReflect g) 0 < 0 := by
    by_contra hnot
    push Not at hnot
    have hfZero : (rlc_dualReflect f) 0 = 0 := by omega
    have hgZero : (rlc_dualReflect g) 0 = 0 := by omega
    rcases face_adj_dir hfgAdj with hg | hg | hg | hg
    · have h0 := congrArg (fun z : Site 2 => z 0) hg
      simp only [Matrix.cons_val_zero] at h0
      omega
    · have h0 := congrArg (fun z : Site 2 => z 0) hg
      simp only [Matrix.cons_val_zero] at h0
      omega
    · apply rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
        gamma gamma' hfaith ((rlc_dualReflect g) 1)
      have hg1 := congrArg (fun z : Site 2 => z 1) hg
      simp only [rlc_dualReflect_one, Matrix.cons_val_one] at hg1
      have hedge : s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![0, (rlc_dualReflect g) 1 - 1] : Site 2),
            ![0, (rlc_dualReflect g) 1]) := by
        rw [Sym2.eq_iff]
        left
        constructor <;> ext i <;> fin_cases i <;> simp_all
      rwa [← hedge]
    · apply rlc_axisVerticalEdge_not_mem_fourTrace_of_faithful
        gamma gamma' hfaith ((rlc_dualReflect f) 1)
      have hg1 := congrArg (fun z : Site 2 => z 1) hg
      simp only [rlc_dualReflect_one, Matrix.cons_val_one] at hg1
      have hedge : s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![0, (rlc_dualReflect f) 1 - 1] : Site 2),
            ![0, (rlc_dualReflect f) 1]) := by
        rw [Sym2.eq_iff]
        right
        constructor <;> ext i <;> fin_cases i <;> simp_all
      rwa [← hedge]
  rcases hsomeNeg with hfNeg | hgNeg
  · have hfNotRight : rlc_dualReflect f ∉
        rlc_pathVertices gamma.1 := by
      intro hfRight
      have hfRect := rlc_pathVertex_mem_rect gamma.1 hfRight
      rw [mem_rect] at hfRect
      omega
    have hfNotFlipLeft : ¬ ∃ z ∈ rlc_pathVertices gamma'.1,
        rlc_dualReflect f = rlc_flipX z := by
      rintro ⟨z, hz, hfz⟩
      have hzRect := rlc_pathVertex_mem_rect gamma'.1 hz
      rw [mem_rect] at hzRect
      have h0 := congrArg (fun x : Site 2 => x 0) hfz
      change (rlc_dualReflect f) 0 = -z 0 at h0
      omega
    exact rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
      gamma gamma' hfgWall (Sym2.mem_mk_left _ _)
        hfNotRight (hpNoLeft f hfP) hfNotFlipLeft
  · have hgNotRight : rlc_dualReflect g ∉
        rlc_pathVertices gamma.1 := by
      intro hgRight
      have hgRect := rlc_pathVertex_mem_rect gamma.1 hgRight
      rw [mem_rect] at hgRect
      omega
    have hgNotFlipLeft : ¬ ∃ z ∈ rlc_pathVertices gamma'.1,
        rlc_dualReflect g = rlc_flipX z := by
      rintro ⟨z, hz, hgz⟩
      have hzRect := rlc_pathVertex_mem_rect gamma'.1 hz
      rw [mem_rect] at hzRect
      have h0 := congrArg (fun x : Site 2 => x 0) hgz
      change (rlc_dualReflect g) 0 = -z 0 at h0
      omega
    exact rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
      gamma gamma' hfgWall (Sym2.mem_mk_right _ _)
        hgNotRight (hpNoLeft g hgP) hgNotFlipLeft


end
end StatMech.Universality
