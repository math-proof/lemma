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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part17
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_goodComponentContacts_or_classifiedBadCarrierSeparationFromLeft
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hsep : RlcCentralFaceFilledBoundaryBadCarrierSeparationFromLeft
      gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryClassifiedBadCarrierSeparationFromLeft
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
  by_cases huInterior : -2 * n < (rlc_dualReflect u) 0 ∧
      (rlc_dualReflect u) 0 < 2 * n ∧
      -n < (rlc_dualReflect u) 1 ∧
      (rlc_dualReflect u) 1 < n
  · have huBarrier :=
      rlc_goodBoundary_bad_exit_near_mem_barrier_of_barrier_start
        hyBarrier hyBox hyu huv hbad huInterior
    rcases rlc_connectorBarrier_original_or_strict_reflected
        gamma gamma' huBarrier with
      huRight | huLeft | huFlipLeft | huFlipRight
    · exact Or.inl ⟨u, y, hyu.symm, huRight, hyPath⟩
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad,
        hvx, Or.inl huLeft⟩
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad,
        hvx, Or.inr (Or.inl huFlipLeft)⟩
    · exact Or.inr ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad,
        hvx, Or.inr (Or.inr (Or.inl huFlipRight))⟩
  · right
    refine ⟨x, y, u, v, hxPath, hyPath, hyu, huv, hbad, hvx,
      Or.inr (Or.inr (Or.inr ?_))⟩
    simp only [rlc_connectorBox, Set.Finite.mem_toFinset] at huBox
    rw [mem_rect] at huBox
    push Not at huInterior
    omega


theorem rlc_goodComponentContacts_or_classifiedBadCarrierSeparationFromLeft_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceFilledBoundaryClassifiedBadCarrierSeparationFromLeft
        gamma gamma' rho := by
  rcases
      rlc_goodComponentContacts_or_badCarrierSeparationFromLeft_of_filledContacts
        gamma gamma' rho
          (rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
            gamma gamma' hfaith rho hno) with hgood | hsep
  · exact Or.inl hgood
  · exact rlc_goodComponentContacts_or_classifiedBadCarrierSeparationFromLeft
      gamma gamma' rho hsep


end
end StatMech.Universality
