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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part32
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRun_reachableLeft_or_axisSuffix_or_strictEntry
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hrun : RlcCentralFaceNegativeWallRunSurgeryAt
      gamma gamma' rho L u)
    (huNeg : (rlc_dualReflect u) 0 < 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma'.1) ∨
      RlcCentralFaceNegativeReflectedRightAxisSuffixAt
        gamma gamma' rho u ∨
      RlcCentralFaceNegativeStrictWallEntryAt gamma gamma' rho L u := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAoff, hentry,
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
  by_cases hleft : ∃ x ∈ r.support,
      rlc_dualReflect x ∈ rlc_pathVertices gamma'.1
  · left
    obtain ⟨x, hx, hxLeft⟩ := hleft
    exact ⟨x, reach_of_mem_r x hx, hxLeft⟩
  · push Not at hleft
    have huNeg' : 0 < -(rlc_dualReflect u) 0 := by omega
    rcases rlc_walk_all_positive_or_last_nonpositive_decomp
        (fun x => -(rlc_dualReflect x) 0) r huNeg' with
      hallNeg | ⟨c, d, pr, s, hcd, hcNonneg, hdNeg,
        hsNeg, hrDecomp⟩
    · right; right
      have hallNeg' : ∀ x ∈ r.support,
          (rlc_dualReflect x) 0 < 0 := by
        intro x hx
        have := hallNeg x hx
        omega
      refine ⟨A, a, b, p, r, hab, hAzero, hAoff, hentry,
        hallNeg', hleft, ?_, hrNotNil⟩
      intro f g hfg
      exact rlc_nonpositive_wallPath_edge_reflectedRight
        hfaith r hrWall hleft
          (fun x hx => le_of_lt (hallNeg' x hx)) hfg
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
      · right; left
        let q : (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Walk c u := .cons hcd s
        have hqSupport : ∀ x ∈ q.support, x ∈ r.support := by
          intro x hx
          rw [hrDecomp, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr hx
        have hqNoLeft : ∀ x ∈ q.support,
            rlc_dualReflect x ∉ rlc_pathVertices gamma'.1 := by
          intro x hx
          exact hleft x (hqSupport x hx)
        have hqWall : ∀ e ∈ q.edges,
            Sym2.map rlc_dualReflect e ∈
              rlc_connectorFourTraceEdges gamma gamma' := by
          intro e he
          apply hrWall e
          rw [hrDecomp, SimpleGraph.Walk.edges_append, List.mem_append]
          exact Or.inr he
        have hqNonpos : ∀ x ∈ q.support,
            (rlc_dualReflect x) 0 ≤ 0 := by
          intro x hx
          simp only [q, SimpleGraph.Walk.support_cons,
            List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact le_of_eq hcZero
          · have := hsNeg x hx
            omega
        have hcRight' : rlc_dualReflect c ∈
            rlc_pathVertices gamma.1 := by
          rwa [hcEq]
        have hcStart := hfaith.right_axis_unique hcRight' hcZero
        refine ⟨c, q, hcStart, hqNoLeft, ?_⟩
        intro f g hfg
        exact rlc_nonpositive_wallPath_edge_reflectedRight
          hfaith q hqWall hqNoLeft hqNonpos hfg
      · left
        have hcR : c ∈ r.support := by
          rw [hrDecomp, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr (SimpleGraph.Walk.cons hcd s).start_mem_support
        exact ⟨c, reach_of_mem_r c hcR, by rwa [hcEq]⟩


theorem rlc_reflectedRightAxisWalk_end_mem_firstIntersectionSuffix
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {c u : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk c u)
    (hcStart : rlc_dualReflect c = (gamma.1.1 : Site 2))
    (hqNoLeft : ∀ x ∈ q.support,
      rlc_dualReflect x ∉ rlc_pathVertices gamma'.1)
    (hqReflectedRight : ∀ {f g : Site 2}, s(f, g) ∈ q.edges →
      s(rlc_dualReflect f, rlc_dualReflect g) ∈
        rlc_reflectedPathEdges gamma.1) :
    ∃ (z : Site 2)
      (hz : rlc_flipX z ∈
        (((rlc_ambientCrossingWalk gamma.1).map
          rlc_flipXLatticeHom).reverse).support),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect u ∈
          ((((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).dropUntil
              (rlc_flipX z) hz).support := by
  obtain ⟨z, hzWR, hzRight, hzLeft, _hfirst, _hglobalMin⟩ :=
    rlc_bookFirstFlippedTraceIntersection_of_faithful
      gamma gamma' hfaith
  let W := ((rlc_ambientCrossingWalk gamma.1).map
    rlc_flipXLatticeHom).reverse
  have hzMapped : rlc_flipX z ∈
      ((rlc_ambientCrossingWalk gamma.1).map
        rlc_flipXLatticeHom).support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    exact ⟨z, hzWR, rfl⟩
  have hzW : rlc_flipX z ∈ W.support := by
    simpa [W, SimpleGraph.Walk.support_reverse] using hzMapped
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
        have hforward :=
          rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
            gamma.1 (hqReflectedRight he0)
        simpa [W, SimpleGraph.Walk.edges_reverse] using hforward
  have hqDualAvoid : rlc_flipX z ∉ qDual.support := by
    intro hzq
    change rlc_flipX z ∈ (q.map hDual).support at hzq
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzq
    obtain ⟨x, hxQ, hxz⟩ := hzq
    change rlc_dualReflect x = rlc_flipX z at hxz
    exact hqNoLeft x hxQ (by simpa [hxz] using hzLeft)
  have hlowerFlip : rlc_flipX (gamma.1.1 : Site 2) =
      (gamma.1.1 : Site 2) :=
    rlc_flipX_eq_self_of_zero gamma.1.1.2.2
  have hcInSuffix : rlc_dualReflect c ∈
      (W.dropUntil (rlc_flipX z) hzW).support := by
    rw [hcStart]
    have hend : rlc_flipX (gamma.1.1 : Site 2) ∈
        (W.dropUntil (rlc_flipX z) hzW).support :=
      (W.dropUntil (rlc_flipX z) hzW).end_mem_support
    rw [hlowerFlip] at hend
    exact hend
  have huSuffix := rlc_walk_end_mem_pathSuffix_of_avoid
    W ((rlc_reflectedAmbientCrossingWalk_isPath gamma.1).reverse)
      hzW qDual hcInSuffix hqDualEdges hqDualAvoid
  exact ⟨z, hzW, hzRight, hzLeft, huSuffix⟩


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRun_reachableLeft_or_firstIntersectionSuffix_or_strictEntry
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hrun : RlcCentralFaceNegativeWallRunSurgeryAt
      gamma gamma' rho L u)
    (huNeg : (rlc_dualReflect u) 0 < 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma'.1) ∨
      (∃ (z : Site 2)
        (hz : rlc_flipX z ∈
          (((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).support),
        z ∈ rlc_pathVertices gamma.1 ∧
          rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
          rlc_dualReflect u ∈
            ((((rlc_ambientCrossingWalk gamma.1).map
              rlc_flipXLatticeHom).reverse).dropUntil
                (rlc_flipX z) hz).support) ∨
      RlcCentralFaceNegativeStrictWallEntryAt gamma gamma' rho L u := by
  rcases L.negativeWallRun_reachableLeft_or_axisSuffix_or_strictEntry
      hfaith hrun huNeg with hleft | haxis | hstrict
  · exact Or.inl hleft
  · right; left
    obtain ⟨c, q, hcStart, hqNoLeft, hqRight⟩ := haxis
    exact rlc_reflectedRightAxisWalk_end_mem_firstIntersectionSuffix
      hfaith q hcStart hqNoLeft hqRight
  · exact Or.inr (Or.inr hstrict)


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.boxBoundary_reachableContacts_or_strictReflectedBarrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    (hu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace u)
    (huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      (∃ y : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace y ∧
          rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
      (∃ z : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace z ∧
          0 < (rlc_dualReflect z) 0 ∧
          ∃ w ∈ rlc_pathVertices gamma'.1,
            rlc_dualReflect z = rlc_flipX w) ∨
      ∃ z : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace z ∧
          (rlc_dualReflect z) 0 < 0 ∧
          ∃ w ∈ rlc_pathVertices gamma.1,
            rlc_dualReflect z = rlc_flipX w := by
  obtain ⟨z, hzReach, hzBarrier⟩ :=
    rlc_goodBoundary_barrier_hit_before_boxBoundary
      L.boundary hfaith hu huBoundary
  rcases rlc_connectorBarrier_original_or_strict_reflected
      gamma gamma' hzBarrier with
    hzRight | hzLeft | hzFlipLeft | hzFlipRight
  · exact Or.inl ⟨z, hzReach, hzRight⟩
  · exact Or.inr (Or.inl ⟨z, hzReach, hzLeft⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨z, hzReach, hzFlipLeft⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨z, hzReach, hzFlipRight⟩))


end
end StatMech.Universality
