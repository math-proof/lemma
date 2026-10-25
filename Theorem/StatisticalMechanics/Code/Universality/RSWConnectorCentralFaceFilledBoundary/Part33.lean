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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part29
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem RlcCentralFaceLowestRetainedAnchoredBoundary.positiveBadExitResidue_boundary_or_axisWallRun_or_lastWallRun
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    (L : RlcCentralFaceLowestRetainedAnchoredBoundary gamma gamma' rho)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {u v : Site 2}
    (q : (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Walk
      L.boundary.secondFace u)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (huv : (faceBoundaryGraph
      (rlc_connectorCentralFaceFilledReachSet gamma gamma' rho)).Adj u v)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hresidue : RlcCentralFacePositiveBadExitResidue
      gamma gamma' rho u v) :
    ((rlc_dualReflect u) 0 = -2 * n ∨
        (rlc_dualReflect u) 0 = 2 * n ∨
        (rlc_dualReflect u) 1 = -n ∨
        (rlc_dualReflect u) 1 = n) ∨
      RlcCentralFacePositiveAxisAllWallRunAt gamma gamma' rho L u ∨
      RlcCentralFacePositiveWallRunSurgeryAt gamma gamma' rho L u := by
  rcases hresidue with hboundary | ⟨w, hw, huw, hallIncoming⟩
  · exact Or.inl hboundary
  · obtain ⟨A, hfirstA, hAfirst, hAzero, hstart⟩ :=
      rlc_goodBoundary_axisAnchor_left_contact_or_offBarrier
        L.boundary hfaith
    obtain ⟨pA⟩ := hAfirst
    let hanchor := L.boundary.anchor_mem_goodBoundaryGraph hfaith
    let Q := pA.append (.cons hanchor q)
    let P : Sym2 (Site 2) → Prop := fun e =>
      Sym2.map rlc_dualReflect e ∈
        rlc_connectorFourTraceEdges gamma gamma'
    rcases rlc_walk_all_edges_or_last_failure_decomp P Q with
      hall | ⟨a, b, p, r, hab, hnotWall, hrWall, hdecomp⟩
    · rcases hstart with hleft | hAoff
      · exact Or.inr (Or.inl ⟨A, Q, hAzero, hleft, hall,
          w, hw, huw⟩)
      · exfalso
        have hANeU : A ≠ u := by
          intro hAu
          have hreflect : rlc_dualReflect A = rlc_dualReflect u :=
            congrArg rlc_dualReflect hAu
          have h0 := congrArg (fun z : Site 2 => z 0) hreflect
          rw [hAzero] at h0
          simp only [Matrix.cons_val_zero] at h0
          omega
        have hQNotNil : ¬ Q.Nil := Q.not_nil_of_ne hANeU
        have hfirstEdge := Q.mk_start_snd_mem_edges hQNotNil
        have hfirstWall := hall _ hfirstEdge
        have hAbarrier := rlc_mem_connectorBarrier_of_mem_fourTraceEdge
          gamma gamma' hfirstWall (by
            change rlc_dualReflect A ∈
              Sym2.map rlc_dualReflect s(A, Q.snd)
            simp [Sym2.map_mk])
        exact hAoff hAbarrier
    · have hrNotNil : ¬ r.Nil := by
        intro hrNil
        have hbu : b = u := hrNil.eq
        subst b
        have hav : a ≠ v := by
          intro hav
          subst a
          apply hbad
          exact (rlc_reflectedEdgeCarrierGeometry_comm
            gamma gamma' v u).1 hab.2
        have hauWall := hallIncoming a hab hav
        apply hnotWall
        simpa [P, Sym2.map_mk] using hauWall
      exact Or.inr (Or.inr ⟨A, a, b, p, r, hab, hAzero, hstart,
        by simpa [P, Sym2.map_mk] using hnotWall, hrWall, hrNotNil,
        w, hw, huw⟩)


end
end StatMech.Universality
