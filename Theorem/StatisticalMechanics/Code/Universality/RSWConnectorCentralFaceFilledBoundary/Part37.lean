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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part33
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem RlcCentralFaceLowestRetainedAnchoredBoundary.boxBoundary_reachableContacts_or_strictResidue
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
      RlcCentralFaceStrictReflectedBarrierResidue gamma gamma' rho L := by
  rcases L.boxBoundary_reachableContacts_or_strictReflectedBarrier
      hfaith hu huBoundary with hright | hleft | hpos | hneg
  · exact Or.inl hright
  · exact Or.inr (Or.inl hleft)
  · right; right
    obtain ⟨z, hzReach, hzPos, w, hw, hzw⟩ := hpos
    exact ⟨z, hzReach, Or.inl ⟨hzPos, w, hw, hzw⟩⟩
  · right; right
    obtain ⟨z, hzReach, hzNeg, w, hw, hzw⟩ := hneg
    exact ⟨z, hzReach, Or.inr ⟨hzNeg, w, hw, hzw⟩⟩


theorem rlc_positiveStrictWallEntry_firstIntersection_sameSide
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hentry : RlcCentralFacePositiveStrictWallEntryAt
      gamma gamma' rho L u) :
    ∃ (z : Site 2)
      (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map
        rlc_flipXLatticeHom).support)
      (b : Site 2),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect b ∈
          ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).support ∧
        rlc_dualReflect u ∈
          ((rlc_ambientCrossingWalk gamma'.1).map
            rlc_flipXLatticeHom).support ∧
        (rlc_dualReflect b ∈
            (((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).dropUntil z hz).support ↔
          rlc_dualReflect u ∈
            (((rlc_ambientCrossingWalk gamma'.1).map
              rlc_flipXLatticeHom).dropUntil z hz).support) := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAstart, hnonwall,
    hrPos, hrNoRight, hrLeft, hrNotNil⟩ := hentry
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
  let rDual : (hypercubicLattice 2).Walk
      (rlc_dualReflect b) (rlc_dualReflect u) := r.map hDual
  have hrDualEdges : ∀ e ∈ rDual.edges, e ∈ W.edges := by
    intro e he
    change e ∈ (r.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    induction e0 using Sym2.inductionOn with
    | _ f g =>
        exact rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
          gamma'.1 (hrLeft he0)
  have hrDualAvoid : z ∉ rDual.support := by
    intro hzq
    change z ∈ (r.map hDual).support at hzq
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzq
    obtain ⟨x, hxR, hxz⟩ := hzq
    change rlc_dualReflect x = z at hxz
    exact hrNoRight x hxR (by simpa [hxz] using hzRight)
  have hfirstEdge := r.mk_start_snd_mem_edges hrNotNil
  have hfirstMapped : s(rlc_dualReflect b,
      rlc_dualReflect r.snd) ∈ W.edges :=
    hrDualEdges _ (by
      change s(rlc_dualReflect b, rlc_dualReflect r.snd) ∈
        (r.map hDual).edges
      rw [SimpleGraph.Walk.edges_map, List.mem_map]
      refine ⟨s(b, r.snd), hfirstEdge, ?_⟩
      rfl)
  have hbW := W.fst_mem_support_of_mem_edges hfirstMapped
  have hlastEdge := r.mk_penultimate_end_mem_edges hrNotNil
  have hlastMapped : s(rlc_dualReflect r.penultimate,
      rlc_dualReflect u) ∈ W.edges :=
    hrDualEdges _ (by
      change s(rlc_dualReflect r.penultimate, rlc_dualReflect u) ∈
        (r.map hDual).edges
      rw [SimpleGraph.Walk.edges_map, List.mem_map]
      refine ⟨s(r.penultimate, u), hlastEdge, ?_⟩
      rfl)
  have huW := W.snd_mem_support_of_mem_edges hlastMapped
  have hsame := rlc_walk_end_mem_pathSuffix_iff_of_avoid
    W (rlc_reflectedAmbientCrossingWalk_isPath gamma'.1)
      hzW rDual hrDualEdges hrDualAvoid
  exact ⟨z, hzW, b, hzRight, hzLeft, hbW, huW, hsame⟩


theorem rlc_negativeStrictWallEntry_firstIntersection_sameSide
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hentry : RlcCentralFaceNegativeStrictWallEntryAt
      gamma gamma' rho L u) :
    ∃ (z : Site 2)
      (hz : rlc_flipX z ∈
        (((rlc_ambientCrossingWalk gamma.1).map
          rlc_flipXLatticeHom).reverse).support)
      (b : Site 2),
      z ∈ rlc_pathVertices gamma.1 ∧
        rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧
        rlc_dualReflect b ∈
          (((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).support ∧
        rlc_dualReflect u ∈
          (((rlc_ambientCrossingWalk gamma.1).map
            rlc_flipXLatticeHom).reverse).support ∧
        (rlc_dualReflect b ∈
            ((((rlc_ambientCrossingWalk gamma.1).map
              rlc_flipXLatticeHom).reverse).dropUntil
                (rlc_flipX z) hz).support ↔
          rlc_dualReflect u ∈
            ((((rlc_ambientCrossingWalk gamma.1).map
              rlc_flipXLatticeHom).reverse).dropUntil
                (rlc_flipX z) hz).support) := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAoff, hnonwall,
    hrNeg, hrNoLeft, hrRight, hrNotNil⟩ := hentry
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
  let rDual : (hypercubicLattice 2).Walk
      (rlc_dualReflect b) (rlc_dualReflect u) := r.map hDual
  have hrDualEdges : ∀ e ∈ rDual.edges, e ∈ W.edges := by
    intro e he
    change e ∈ (r.map hDual).edges at he
    rw [SimpleGraph.Walk.edges_map, List.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    induction e0 using Sym2.inductionOn with
    | _ f g =>
        have hforward :=
          rlc_mem_reflectedAmbientCrossingWalk_edges_of_mem_reflectedPathEdges
            gamma.1 (hrRight he0)
        simpa [W, SimpleGraph.Walk.edges_reverse] using hforward
  have hrDualAvoid : rlc_flipX z ∉ rDual.support := by
    intro hzq
    change rlc_flipX z ∈ (r.map hDual).support at hzq
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hzq
    obtain ⟨x, hxR, hxz⟩ := hzq
    change rlc_dualReflect x = rlc_flipX z at hxz
    exact hrNoLeft x hxR (by simpa [hxz] using hzLeft)
  have hfirstEdge := r.mk_start_snd_mem_edges hrNotNil
  have hfirstMapped : s(rlc_dualReflect b,
      rlc_dualReflect r.snd) ∈ W.edges :=
    hrDualEdges _ (by
      change s(rlc_dualReflect b, rlc_dualReflect r.snd) ∈
        (r.map hDual).edges
      rw [SimpleGraph.Walk.edges_map, List.mem_map]
      refine ⟨s(b, r.snd), hfirstEdge, ?_⟩
      rfl)
  have hbW := W.fst_mem_support_of_mem_edges hfirstMapped
  have hlastEdge := r.mk_penultimate_end_mem_edges hrNotNil
  have hlastMapped : s(rlc_dualReflect r.penultimate,
      rlc_dualReflect u) ∈ W.edges :=
    hrDualEdges _ (by
      change s(rlc_dualReflect r.penultimate, rlc_dualReflect u) ∈
        (r.map hDual).edges
      rw [SimpleGraph.Walk.edges_map, List.mem_map]
      refine ⟨s(r.penultimate, u), hlastEdge, ?_⟩
      rfl)
  have huW := W.snd_mem_support_of_mem_edges hlastMapped
  have hsame := rlc_walk_end_mem_pathSuffix_iff_of_avoid
    W ((rlc_reflectedAmbientCrossingWalk_isPath gamma.1).reverse)
      hzW rDual hrDualEdges hrDualAvoid
  exact ⟨z, hzW, b, hzRight, hzLeft, hbW, huW, hsame⟩


theorem rlc_positiveStrictWallEntry_regionFlank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hentry : RlcCentralFacePositiveStrictWallEntryAt
      gamma gamma' rho L u) :
    ∃ (a b : Site 2),
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b ∧
        s(rlc_dualReflect a, rlc_dualReflect b) ∉
          rlc_connectorFourTraceEdges gamma gamma' ∧
        rlc_dualReflect a ∈ rlc_connectorBox n ∧
        rlc_dualReflect b ∈ rlc_connectorBox n ∧
        ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
          h ∈ flankFaces (rlc_dualReflect a) (rlc_dualReflect b) := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAstart, hnonwall,
    hrPos, hrNoRight, hrLeft, hrNotNil⟩ := hentry
  refine ⟨a, b, hab, hnonwall, ?_⟩
  rcases hab.2 with hwall | hregion
  · exact False.elim (hnonwall hwall)
  · exact hregion


theorem rlc_negativeStrictWallEntry_regionFlank
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u : Site 2}
    (hentry : RlcCentralFaceNegativeStrictWallEntryAt
      gamma gamma' rho L u) :
    ∃ (a b : Site 2),
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a b ∧
        s(rlc_dualReflect a, rlc_dualReflect b) ∉
          rlc_connectorFourTraceEdges gamma gamma' ∧
        rlc_dualReflect a ∈ rlc_connectorBox n ∧
        rlc_dualReflect b ∈ rlc_connectorBox n ∧
        ∃ h ∈ rlc_connectorCentralFaceRegion gamma gamma',
          h ∈ flankFaces (rlc_dualReflect a) (rlc_dualReflect b) := by
  obtain ⟨A, a, b, p, r, hab, hAzero, hAoff, hnonwall,
    hrNeg, hrNoLeft, hrRight, hrNotNil⟩ := hentry
  refine ⟨a, b, hab, hnonwall, ?_⟩
  rcases hab.2 with hwall | hregion
  · exact False.elim (hnonwall hwall)
  · exact hregion


end
end StatMech.Universality
