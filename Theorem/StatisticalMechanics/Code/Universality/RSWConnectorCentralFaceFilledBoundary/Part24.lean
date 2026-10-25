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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part20
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_goodComponentContacts_or_reducedBadCarrierSeparationFromLeft
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma')
    (hsep : RlcCentralFaceFilledBoundaryBadCarrierSeparationFromLeft
      gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryReducedBadCarrierSeparationFromLeft
        gamma gamma' rho := by
  obtain ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad, hvx⟩ := hsep
  have hyBarrier : rlc_dualReflect y ∈
      rlc_connectorBarrier gamma gamma' := by
    simp [rlc_connectorBarrier, hyPath]
  have hyBox : rlc_dualReflect y ∈ rlc_connectorBox n := by
    have hrect := rlc_pathVertex_mem_rect gamma'.1 hyPath
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset]
    rw [mem_rect] at hrect ⊢
    omega
  have huBox : rlc_dualReflect u ∈ rlc_connectorBox n :=
    rlc_goodBoundary_reachable_dualReflect_mem_box_of_start hyBox hyu
  by_cases huBoundary : (rlc_dualReflect u) 0 = -2 * n ∨
      (rlc_dualReflect u) 0 = 2 * n ∨
      (rlc_dualReflect u) 1 = -n ∨
      (rlc_dualReflect u) 1 = n
  · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad, hvx,
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
        hyBarrier hyBox hyu huv hbad huInterior
    rcases rlc_connectorBarrier_original_or_strict_reflected
        gamma gamma' huBarrier with
      huRight | huLeft | huFlipLeft | huFlipRight
    · exact Or.inl ⟨u, y, hyu.symm, huRight, hyPath⟩
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad, hvx,
        Or.inl huLeft⟩
    · by_cases hwall : RlcCentralFaceBadExitAllIncomingWall
          gamma gamma' rho u v
      · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad, hvx,
          Or.inr (Or.inr (Or.inr hwall))⟩
      · simp only [RlcCentralFaceBadExitAllIncomingWall, not_forall] at hwall
        obtain ⟨a, hau, hav, hnotWall⟩ := hwall
        have huRight := rlc_positiveBarrier_bad_exit_forces_right_contact
          gamma gamma' rho hno hau.1 hau.2 huv hav hnotWall
            huFlipLeft.1 huBarrier huInterior hbad
        exact Or.inl ⟨u, y, hyu.symm, huRight, hyPath⟩
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad, hvx,
        Or.inr (Or.inl huFlipRight)⟩


theorem rlc_goodComponentContacts_or_reducedBadCarrierSeparation_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryReducedBadCarrierSeparation
        gamma gamma' rho := by
  rcases
      rlc_goodComponentContacts_or_badCarrierSeparation_of_faithful_failure
        gamma gamma' hfaith rho hno with hgood | hsep
  · exact Or.inl hgood
  · exact rlc_goodComponentContacts_or_reducedBadCarrierSeparation
      gamma gamma' rho hno hsep


theorem rlc_goodComponentContacts_or_reducedBadCarrierSeparationFromLeft_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryReducedBadCarrierSeparationFromLeft
        gamma gamma' rho := by
  rcases
      rlc_goodComponentContacts_or_badCarrierSeparationFromLeft_of_filledContacts
        gamma gamma' rho
          (rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
            gamma gamma' hfaith rho hno) with hgood | hsep
  · exact Or.inl hgood
  · exact rlc_goodComponentContacts_or_reducedBadCarrierSeparationFromLeft
      gamma gamma' rho hno hsep


theorem rlc_goodComponentContacts_or_twoSidedReducedBadCarrierSeparation_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      (RlcCentralFaceFilledBoundaryReducedBadCarrierSeparation
          gamma gamma' rho ∧
        RlcCentralFaceFilledBoundaryReducedBadCarrierSeparationFromLeft
          gamma gamma' rho) := by
  rcases
      rlc_goodComponentContacts_or_reducedBadCarrierSeparation_of_faithful_failure
        gamma gamma' hfaith rho hno with hgood | hright
  · exact Or.inl hgood
  · rcases
        rlc_goodComponentContacts_or_reducedBadCarrierSeparationFromLeft_of_faithful_failure
          gamma gamma' hfaith rho hno with hgood | hleft
    · exact Or.inl hgood
    · exact Or.inr ⟨hright, hleft⟩


end
end StatMech.Universality
