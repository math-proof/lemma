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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part25
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoSignedBadExits_PIMS_or_exactResidue
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u' v')
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
        rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨
      RlcCentralFaceNegativeBadExitResidue gamma gamma' rho u v ∨
      RlcCentralFacePositiveBadExitResidue gamma gamma' rho u' v' := by
  have huReach := q.reachable
  have hu'Reach :=
    (L.boundary.anchor_mem_goodBoundaryGraph hfaith).reachable.trans q'.reachable
  rcases L.negativeBadExit_reachable_left_or_boundary_or_reflectedRightWall
      hfaith hno huReach huNeg huv hbad with
    hleft | hnegativeBoundary | hnegativeWall
  · rcases L.positiveBadExit_reachable_right_or_boundary_or_reflectedLeftWall
        hfaith hno hu'Reach hu'Pos hu'v' hbad' with
      hright | hpositiveBoundary | hpositiveWall
    · left
      obtain ⟨y, hyReach, hyPath⟩ := hleft
      obtain ⟨x, hxReach, hxPath⟩ := hright
      apply rlc_centralFacePIMS_success_of_goodComponentContacts
        gamma gamma' rho
      exact ⟨x, y, hxReach.symm.trans hyReach, hxPath, hyPath⟩
    · exact Or.inr (Or.inr (Or.inl hpositiveBoundary))
    · exact Or.inr (Or.inr (Or.inr hpositiveWall))
  · exact Or.inr (Or.inl (Or.inl hnegativeBoundary))
  · exact Or.inr (Or.inl (Or.inr hnegativeWall))


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoSignedBadExits_PIMS_or_reachableBarrier
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u' v')
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
        rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨
      ∃ z : Site 2,
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            L.boundary.firstFace z ∧
          rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
  have huReach := q.reachable
  have hu'Reach :=
    (L.boundary.anchor_mem_goodBoundaryGraph hfaith).reachable.trans q'.reachable
  rcases L.negativeBadExit_reachable_left_or_barrier
      hfaith hno huReach huNeg huv hbad with hleft | hbarrier
  · rcases L.positiveBadExit_reachable_right_or_barrier
        hfaith hno hu'Reach hu'Pos hu'v' hbad' with hright | hbarrier
    · left
      obtain ⟨y, hyReach, hyPath⟩ := hleft
      obtain ⟨x, hxReach, hxPath⟩ := hright
      apply rlc_centralFacePIMS_success_of_goodComponentContacts
        gamma gamma' rho
      exact ⟨x, y, hxReach.symm.trans hyReach, hxPath, hyPath⟩
    · exact Or.inr hbarrier
  · exact Or.inr hbarrier


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_PIMS_or_reachableBarrier
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
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0) :
    (∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ L.boundary.contour.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k)) ∧
      (rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
          rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨
        ∃ z : Site 2,
          (rlc_connectorCentralFaceGoodBoundaryGraph
              gamma gamma' rho).Reachable L.boundary.firstFace z ∧
            rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') := by
  constructor
  · exact L.twoBadMiddle_axis_crossing_extreme haExact haAvoid q r huv
      hdecomp q' t hu'v' hdecomp' huNeg hu'Pos
  · exact L.twoSignedBadExits_PIMS_or_reachableBarrier
      hfaith hno q q' huv hbad hu'v' hbad' huNeg hu'Pos


theorem RlcCentralFaceLowestRetainedAnchoredBoundary.twoBadMiddle_extreme_and_PIMS_or_exactResidue
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
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    {u v u' v' : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.firstFace u)
    (r : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk
        v L.boundary.secondFace)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hdecomp : a = (q.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons huv r))
    (q' : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u')
    (t : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Walk v' v)
    (hu'v' : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u' v')
    (hbad' : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u' v')
    (hdecomp' : r.reverse = (q'.mapLe
      (rlc_connectorCentralFaceGoodBoundaryGraph_le gamma gamma' rho)).append
        (.cons hu'v' t))
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hu'Pos : 0 < (rlc_dualReflect u') 0) :
    (∃ (f g : Site 2) (k : Int),
      s(f, g) ∈ L.boundary.contour.edges ∧
        s(rlc_dualReflect f, rlc_dualReflect g) =
          s((![-1, k] : Site 2), ![0, k]) ∧
        (k ≤ (gamma.1.1 : Site 2) 1 ∨
          L.boundary.height + 1 < k)) ∧
      (rlc_connectorCentralFacePIMSConfig gamma gamma' rho ∈
          rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' ∨
        RlcCentralFaceNegativeBadExitResidue gamma gamma' rho u v ∨
        RlcCentralFacePositiveBadExitResidue gamma gamma' rho u' v') := by
  constructor
  · exact L.twoBadMiddle_axis_crossing_extreme haExact haAvoid q r huv
      hdecomp q' t hu'v' hdecomp' huNeg hu'Pos
  · exact L.twoSignedBadExits_PIMS_or_exactResidue
      hfaith hno q q' huv hbad hu'v' hbad' huNeg hu'Pos


end
end StatMech.Universality
