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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part19
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_goodComponentContacts_or_reducedBadCarrierSeparation
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    (hsep : RlcCentralFaceFilledBoundaryBadCarrierSeparation
      gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryReducedBadCarrierSeparation
        gamma gamma' rho := by
  obtain ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hbad, hvy⟩ := hsep
  have hxBarrier : rlc_dualReflect x ∈
      rlc_connectorBarrier gamma gamma' := by
    simp [rlc_connectorBarrier, hxPath]
  have hxBox : rlc_dualReflect x ∈ rlc_connectorBox n := by
    have hrect := rlc_pathVertex_mem_rect gamma.1 hxPath
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect] at hrect ⊢
    omega
  have huBox : rlc_dualReflect u ∈ rlc_connectorBox n :=
    rlc_goodBoundary_reachable_dualReflect_mem_box_of_start hxBox hxu
  by_cases huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n
  · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hbad, hvy,
      Or.inr (Or.inr (Or.inl huBoundary))⟩
  · have huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
        (rlc_dualReflect u) 0 < 2 * n ∧
        -n < (rlc_dualReflect u) 1 ∧
        (rlc_dualReflect u) 1 < n := by
      simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
      rw [mem_rect] at huBox
      push Not at huBoundary
      omega
    have huBarrier :=
      rlc_goodBoundary_bad_exit_near_mem_barrier_of_barrier_start
        hxBarrier hxBox hxu huv hbad huInterior
    rcases rlc_connectorBarrier_original_or_strict_reflected
        gamma gamma' huBarrier with
      huRight | huLeft | huFlipLeft | huFlipRight
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hbad, hvy,
        Or.inl huRight⟩
    · exact Or.inl ⟨x, u, hxu, hxPath, huLeft⟩
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hbad, hvy,
        Or.inr (Or.inl huFlipLeft)⟩
    · by_cases hwall : RlcCentralFaceBadExitAllIncomingWall
          gamma gamma' rho u v
      · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hxu, huv, hbad, hvy,
          Or.inr (Or.inr (Or.inr hwall))⟩
      · simp only [RlcCentralFaceBadExitAllIncomingWall, not_forall] at hwall
        obtain ⟨a, hau, hav, hnotWall⟩ := hwall
        have huLeft := rlc_negativeBarrier_bad_exit_forces_left_contact
          gamma gamma' rho hno hau.1 hau.2 huv hav hnotWall
            huFlipRight.1 huBarrier huInterior hbad
        exact Or.inl ⟨x, u, hxu, hxPath, huLeft⟩


end
end StatMech.Universality
