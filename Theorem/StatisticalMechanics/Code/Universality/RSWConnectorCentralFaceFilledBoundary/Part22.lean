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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part18
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_badExit_exists_incomingWall_of_reachable
    {n : Int} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {rho : ConfigSpace (Sym2 (RlcConnectorVertex n))}
    {x u v : Site 2}
    (hxu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable x u)
    (hxuNe : x ≠ u)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (hwall : RlcCentralFaceBadExitAllIncomingWall
      gamma gamma' rho u v) :
    ∃ a : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a u ∧
        a ≠ v ∧
        s(rlc_dualReflect a, rlc_dualReflect u) ∈
          rlc_connectorFourTraceEdges gamma gamma' := by
  obtain ⟨p⟩ := hxu.symm
  cases p with
  | nil => exact False.elim (hxuNe rfl)
  | @cons a b c hab p =>
      have hba := hab.symm
      have hbNe : b ≠ v := by
        intro hbv
        subst b
        exact hbad hab.2
      exact ⟨b, hba, hbNe, hwall b hba hbNe⟩


theorem rlc_rightBased_negative_badExit_incoming_reflectedRight
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hnoGood : ¬ RlcCentralFaceFilledBoundaryGoodComponentContacts
      gamma gamma' rho)
    {x u v : Site 2}
    (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
    (hxu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable x u)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (huNeg : (rlc_dualReflect u) 0 < 0)
    (hwall : RlcCentralFaceBadExitAllIncomingWall
      gamma gamma' rho u v) :
    ∃ a : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a u ∧
        a ≠ v ∧
        s(rlc_dualReflect a, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma.1 := by
  have hxuNe : x ≠ u := by
    intro hxuEq
    subst u
    have hxRect := rlc_pathVertex_mem_rect gamma.1 hxPath
    rw [mem_rect] at hxRect
    omega
  obtain ⟨a, hau, hav, hauWall⟩ :=
    rlc_badExit_exists_incomingWall_of_reachable hxu hxuNe hbad hwall
  have huRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1 := by
    intro hu
    have huRect := rlc_pathVertex_mem_rect gamma.1 hu
    rw [mem_rect] at huRect
    omega
  have huLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1 := by
    intro hu
    exact hnoGood ⟨x, u, hxu, hxPath, hu⟩
  have huFlipLeft : ¬ ∃ w ∈ rlc_pathVertices gamma'.1,
      rlc_dualReflect u = rlc_flipX w := by
    rintro ⟨w, hw, huw⟩
    have hwRect := rlc_pathVertex_mem_rect gamma'.1 hw
    rw [mem_rect] at hwRect
    have huw0 := congrArg (fun z : Site 2 => z 0) huw
    have huNeg' := huNeg
    simp [rlc_dualReflect, rlc_dualReflectFun] at huNeg'
    simp [rlc_flipX, rlc_flipXFun] at huw0
    omega
  refine ⟨a, hau, hav, ?_⟩
  exact rlc_fourTraceEdge_mem_reflectedRight_of_endpoint_exclusive
    gamma gamma' hauWall (Sym2.mem_mk_right _ _)
      huRight huLeft huFlipLeft


theorem rlc_leftBased_positive_badExit_incoming_reflectedLeft
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hnoGood : ¬ RlcCentralFaceFilledBoundaryGoodComponentContacts
      gamma gamma' rho)
    {y u v : Site 2}
    (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
    (hyu : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable y u)
    (hbad : ¬ RlcCentralFaceReflectedEdgeCarrierGeometry
      gamma gamma' u v)
    (huPos : 0 < (rlc_dualReflect u) 0)
    (hwall : RlcCentralFaceBadExitAllIncomingWall
      gamma gamma' rho u v) :
    ∃ a : Site 2,
      (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Adj a u ∧
        a ≠ v ∧
        s(rlc_dualReflect a, rlc_dualReflect u) ∈
          rlc_reflectedPathEdges gamma'.1 := by
  have hyuNe : y ≠ u := by
    intro hyuEq
    subst u
    have hyRect := rlc_pathVertex_mem_rect gamma'.1 hyPath
    rw [mem_rect] at hyRect
    omega
  obtain ⟨a, hau, hav, hauWall⟩ :=
    rlc_badExit_exists_incomingWall_of_reachable hyu hyuNe hbad hwall
  have huRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1 := by
    intro hu
    exact hnoGood ⟨u, y, hyu.symm, hu, hyPath⟩
  have huLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1 := by
    intro hu
    have huRect := rlc_pathVertex_mem_rect gamma'.1 hu
    rw [mem_rect] at huRect
    omega
  have huFlipRight : ¬ ∃ w ∈ rlc_pathVertices gamma.1,
      rlc_dualReflect u = rlc_flipX w := by
    rintro ⟨w, hw, huw⟩
    have hwRect := rlc_pathVertex_mem_rect gamma.1 hw
    rw [mem_rect] at hwRect
    have huw0 := congrArg (fun z : Site 2 => z 0) huw
    have huPos' := huPos
    simp [rlc_dualReflect, rlc_dualReflectFun] at huPos'
    simp [rlc_flipX, rlc_flipXFun] at huw0
    omega
  refine ⟨a, hau, hav, ?_⟩
  exact rlc_fourTraceEdge_mem_reflectedLeft_of_endpoint_exclusive
    gamma gamma' hauWall (Sym2.mem_mk_right _ _)
      huRight huLeft huFlipRight


end
end StatMech.Universality
