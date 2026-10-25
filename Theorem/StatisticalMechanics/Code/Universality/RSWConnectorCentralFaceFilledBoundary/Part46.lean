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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part42
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_pairedStrictWallEntryDecomp_boundary_or_nonwall_or_orderedSides
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u v u' v' : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    {q' : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u'}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q')
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u' v') :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        ((rlc_dualReflect x) 0 = -2 * n ∨
          (rlc_dualReflect x) 0 = 2 * n ∨
          (rlc_dualReflect x) 1 = -n ∨
          (rlc_dualReflect x) 1 = n)) ∨
      (∃ f g : Site 2,
        s(f, g) ∈ L.boundary.contour.edges ∧
          RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧
          s(rlc_dualReflect f, rlc_dualReflect g) ∉
            rlc_connectorFourTraceEdges gamma gamma') ∨
      ((∃ t h t' h' k k' : Site 2,
        h ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
          h' ∈ rlc_connectorCentralFaceRegion gamma gamma' ∧
          flankFaces (rlc_dualReflect t) (rlc_dualReflect u) = s(h, k) ∧
          flankFaces (rlc_dualReflect t') (rlc_dualReflect u') = s(h', k') ∧
          (let C := (L.boundary.contour.mapLe
            (faceBoundaryGraph_le
              (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho))).map
                rlc_dualReflectLatticeHom
           (phb_doubleDualEquiv.symm h ∈ jec_leftRegion C ↔
              phb_doubleDualEquiv.symm h' ∈ jec_leftRegion C) ∧
            (phb_doubleDualEquiv.symm k ∈ jec_leftRegion C ↔
              phb_doubleDualEquiv.symm k' ∈ jec_leftRegion C))) ∧
        RlcCentralFacePairedFirstIntersectionSideData gamma gamma' u u') := by
  exact Or.inr (Or.inl hneg.nonwallGoodContourEdge)


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_boundary_or_pairedTerminal
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0)
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q)
    (hpos : RlcCentralFacePositiveStrictWallEntryDecompAt
      gamma gamma' rho L q') :
    (∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ L.boundary.contour.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k)) ∧
      ((∃ x : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace x ∧
          ((rlc_dualReflect x) 0 = -2 * n ∨
            (rlc_dualReflect x) 0 = 2 * n ∨
            (rlc_dualReflect x) 1 = -n ∨
            (rlc_dualReflect x) 1 = n)) ∨
        RlcCentralFacePairedTerminalSideChange
          gamma gamma' rho L u v u' v') := by
  constructor
  · exact L.twoBadMiddle_axis_crossing_extreme haExact haAvoid q r huv
      hdecomp q' t hu'v' hdecomp' huNeg hu'Pos
  · exact rlc_pairedStrictWallEntryDecomp_boundary_or_terminalSideChange
      hfaith hneg hpos huv hbad hu'v' hbad'


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_nonwallGoodContourEdge
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0)
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    (∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ L.boundary.contour.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k)) ∧
      ∃ f g : Site 2,
        s(f, g) ∈ L.boundary.contour.edges ∧
          RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g ∧
          s(rlc_dualReflect f, rlc_dualReflect g) ∉
            rlc_connectorFourTraceEdges gamma gamma' := by
  exact ⟨L.twoBadMiddle_axis_crossing_extreme haExact haAvoid q r huv
      hdecomp q' t hu'v' hdecomp' huNeg hu'Pos,
    hneg.nonwallGoodContourEdge⟩


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_goodComponentContacts_or_missingIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0)
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    (∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ L.boundary.contour.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k)) ∧
      (RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
        ∃ f g : Site 2,
          RlcCentralFaceNonwallGoodContourEdgeMissingContactIncidence
            L.boundary f g) := by
  obtain ⟨hextreme, f, g, hfgContour, hcarrier, hnonwall⟩ :=
    L.twoBadMiddle_extreme_and_nonwallGoodContourEdge
      haExact haAvoid q r huv hdecomp q' t hu'v' hdecomp'
        huNeg hu'Pos hneg
  refine ⟨hextreme, ?_⟩
  rcases rlc_goodComponentContacts_or_nonwallEdgeMissingContactIncidence
      hfgContour hcarrier hnonwall with hgood | hmissing
  · exact Or.inl hgood
  · exact Or.inr ⟨f, g, hmissing⟩


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_goodComponentContacts_or_anchoredMissingIncidence
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    {a : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        L.boundary.firstFace L.boundary.secondFace}
    (haExact : ∀ e : Sym2 (Site 2),
      e ∈ L.boundary.contour.edges ↔
        e = s(L.boundary.firstFace, L.boundary.secondFace) ∨ e ∈ a.edges)
    (haAvoid : s(L.boundary.firstFace, L.boundary.secondFace) ∉ a.edges)
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0)
    (hneg : RlcCentralFaceNegativeStrictWallEntryDecompAt
      gamma gamma' rho L q) :
    (∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ L.boundary.contour.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k)) ∧
      (RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
        ∃ f g : Site 2,
          RlcCentralFaceAnchoredNonwallGoodContourEdgeMissingContactIncidence
            L.boundary f g) := by
  have hextreme := L.twoBadMiddle_axis_crossing_extreme
    haExact haAvoid q r huv hdecomp q' t hu'v' hdecomp' huNeg hu'Pos
  obtain ⟨f, g, hfgContour, hcarrier, hnonwall, hfirstF, hfirstG⟩ :=
    hneg.anchoredNonwallGoodContourEdge
  refine ⟨hextreme, ?_⟩
  rcases rlc_goodComponentContacts_or_anchoredNonwallEdgeMissingContactIncidence
      hfgContour hcarrier hnonwall hfirstF hfirstG with hgood | hmissing
  · exact Or.inl hgood
  · exact Or.inr ⟨f, g, hmissing⟩


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRunDecomp_reachableRight_or_axisSuffix_or_strictEntryDecomp
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.secondFace u}
    (hrun : RlcCentralFacePositiveWallRunDecompAt
      gamma gamma' rho L q)
    (huPos : 0 < (rlc_dualReflect u) 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma.1) ∨
      RlcCentralFacePositiveReflectedLeftAxisSuffixAt
        gamma gamma' rho u ∨
      RlcCentralFacePositiveStrictWallEntryDecompAt
        gamma gamma' rho L q := by
  obtain ⟨A, a, b, pA, p, r, hanchor, hab, hdecomp, hAzero,
    hAstart, hentry, hrWall, hrNotNil, w, hw, huw⟩ := hrun
  have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace A := ⟨pA.reverse⟩
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
      refine ⟨A, a, b, pA, p, r, hanchor, hab, hdecomp,
        hAzero, hAstart, hentry, hallPos, hright, ?_, hrNotNil⟩
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
        exact ⟨c, reach_of_mem_r c hcR, by rwa [hcEq]⟩
      · right; left
        let t : (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Walk c u := .cons hcd s
        have htSupport : ∀ x ∈ t.support, x ∈ r.support := by
          intro x hx
          rw [hrDecomp, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr hx
        have htNoRight : ∀ x ∈ t.support,
            rlc_dualReflect x ∉ rlc_pathVertices gamma.1 := by
          intro x hx
          exact hright x (htSupport x hx)
        have htWall : ∀ e ∈ t.edges,
            Sym2.map rlc_dualReflect e ∈
              rlc_connectorFourTraceEdges gamma gamma' := by
          intro e he
          apply hrWall e
          rw [hrDecomp, SimpleGraph.Walk.edges_append, List.mem_append]
          exact Or.inr he
        have htNonneg : ∀ x ∈ t.support,
            0 ≤ (rlc_dualReflect x) 0 := by
          intro x hx
          simp only [t, SimpleGraph.Walk.support_cons,
            List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact le_of_eq hcZero.symm
          · exact le_of_lt (hsPos x hx)
        have hcLeft' : rlc_dualReflect c ∈
            rlc_pathVertices gamma'.1 := by
          rwa [hcEq]
        have hcEnd := hfaith.left_axis_unique hcLeft' hcZero
        refine ⟨c, t, hcEnd, htNoRight, ?_⟩
        intro f g hfg
        exact rlc_nonnegative_wallPath_edge_reflectedLeft
          hfaith t htWall htNoRight htNonneg hfg


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRunDecomp_reachableLeft_or_axisSuffix_or_strictEntryDecomp
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u : Site 2}
    {q : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Walk L.boundary.firstFace u}
    (hrun : RlcCentralFaceNegativeWallRunDecompAt
      gamma gamma' rho L q)
    (huNeg : (rlc_dualReflect u) 0 < 0) :
    (∃ x : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace x ∧
        rlc_dualReflect x ∈ rlc_pathVertices gamma'.1) ∨
      RlcCentralFaceNegativeReflectedRightAxisSuffixAt
        gamma gamma' rho u ∨
      RlcCentralFaceNegativeStrictWallEntryDecompAt
        gamma gamma' rho L q := by
  obtain ⟨A, a, b, pA, p, r, hab, hdecomp, hAzero, hAoff,
    hentry, hrWall, hrNotNil, w, hw, huw⟩ := hrun
  have hfirstA : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable L.boundary.firstFace A := ⟨pA.reverse⟩
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
      refine ⟨A, a, b, pA, p, r, hab, hdecomp, hAzero, hAoff,
        hentry, hallNeg', hleft, ?_, hrNotNil⟩
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
        let t : (rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Walk c u := .cons hcd s
        have htSupport : ∀ x ∈ t.support, x ∈ r.support := by
          intro x hx
          rw [hrDecomp, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr hx
        have htNoLeft : ∀ x ∈ t.support,
            rlc_dualReflect x ∉ rlc_pathVertices gamma'.1 := by
          intro x hx
          exact hleft x (htSupport x hx)
        have htWall : ∀ e ∈ t.edges,
            Sym2.map rlc_dualReflect e ∈
              rlc_connectorFourTraceEdges gamma gamma' := by
          intro e he
          apply hrWall e
          rw [hrDecomp, SimpleGraph.Walk.edges_append, List.mem_append]
          exact Or.inr he
        have htNonpos : ∀ x ∈ t.support,
            (rlc_dualReflect x) 0 ≤ 0 := by
          intro x hx
          simp only [t, SimpleGraph.Walk.support_cons,
            List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact le_of_eq hcZero
          · have := hsNeg x hx
            omega
        have hcRight' : rlc_dualReflect c ∈
            rlc_pathVertices gamma.1 := by
          rwa [hcEq]
        have hcStart := hfaith.right_axis_unique hcRight' hcZero
        refine ⟨c, t, hcStart, htNoLeft, ?_⟩
        intro f g hfg
        exact rlc_nonpositive_wallPath_edge_reflectedRight
          hfaith t htWall htNoLeft htNonpos hfg
      · left
        have hcR : c ∈ r.support := by
          rw [hrDecomp, SimpleGraph.Walk.mem_support_append_iff]
          exact Or.inr (SimpleGraph.Walk.cons hcd s).start_mem_support
        exact ⟨c, reach_of_mem_r c hcR, by rwa [hcEq]⟩


theorem rlc_strictSurgeryResidue_of_strictCarrierSurgeryResidue
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho}
    {u v u' v' : Site 2}
    (h : RlcCentralFaceStrictCarrierSurgeryResidue
      gamma gamma' rho L u v u' v') :
    RlcCentralFaceStrictSurgeryResidue gamma gamma' rho L u u' := by
  rcases h with hneg | hpos | hbarrier
  · exact Or.inl hneg.1
  · exact Or.inr (Or.inl hpos.1)
  · exact Or.inr (Or.inr hbarrier)


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveWallRun_reachableRight_or_firstIntersectionSuffix_or_strictCarrierSurgery
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u v : Site 2}
    (hrun : RlcCentralFacePositiveWallRunSurgeryAt
      gamma gamma' rho L u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
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
      RlcCentralFacePositiveStrictCarrierSurgeryAt
        gamma gamma' rho L u v := by
  rcases L.positiveWallRun_reachableRight_or_firstIntersectionSuffix_or_strictEntry
      hfaith hrun huPos with hright | hsuffix | hstrict
  · exact Or.inl hright
  · exact Or.inr (Or.inl hsuffix)
  · exact Or.inr (Or.inr ⟨hstrict, huv, hbad⟩)


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.negativeWallRun_reachableLeft_or_firstIntersectionSuffix_or_strictCarrierSurgery
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u v : Site 2}
    (hrun : RlcCentralFaceNegativeWallRunSurgeryAt
      gamma gamma' rho L u)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v) :
    (∃ y : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
          L.boundary.firstFace y ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) ∨
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
      RlcCentralFaceNegativeStrictCarrierSurgeryAt
        gamma gamma' rho L u v := by
  rcases L.negativeWallRun_reachableLeft_or_firstIntersectionSuffix_or_strictEntry
      hfaith hrun huNeg with hleft | hsuffix | hstrict
  · exact Or.inl hleft
  · exact Or.inr (Or.inl hsuffix)
  · exact Or.inr (Or.inr ⟨hstrict, huv, hbad⟩)

end
end StatMech.Universality
