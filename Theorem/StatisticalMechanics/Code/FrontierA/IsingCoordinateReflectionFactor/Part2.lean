/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCoordinateReflectionFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionDomain.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingCoordinateReflectionFactor.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section

variable (K : Finset (Site d)) (i : Fin d) (m : Int)

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingCoordinateReflect i m x ∈ K)


theorem isingCoordinateDomainWeight_factor
    (beta : Real)
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m)) :
    isingWeight (freeDomainGraph K) beta 0
        (isingCoordinateDomainGlue K i m hK boundary lower upper) =
      isingCoordinateDomainHalfWeight K i m hK beta boundary lower *
        isingCoordinateDomainHalfWeight K i m hK beta boundary upper *
        Real.exp (-beta *
          (isingCoordinateDomainCrossBoundary K i m hK).card) *
        Real.exp (beta * ∑ z ∈
          isingCoordinateDomainCrossBoundary K i m hK,
            spin lower z * spin upper z) := by
  unfold isingWeight isingCoordinateDomainHalfWeight
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  have hcorr := isingCoordinateDomain_hamiltonian_cross_correction
    K i m hK boundary lower upper
  have hsplit :
      (∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK,
        (1 - spin lower z * spin upper z)) =
      ((isingCoordinateDomainCrossBoundary K i m hK).card : Real) -
        ∑ z ∈ isingCoordinateDomainCrossBoundary K i m hK,
          spin lower z * spin upper z := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hsplit] at hcorr
  linear_combination (-beta / 2) * hcorr

end
end StatMech.FrontierA
