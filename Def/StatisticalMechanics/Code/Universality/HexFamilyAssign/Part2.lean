/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFamilyAssign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexContourDecomp.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexFamilyAssign.Part2


namespace StatMech.Universality

open Complex

open scoped BigOperators


noncomputable def hexCell (c : ℂ) : HexDomain (Fin 1) where
  interiorVertices := {0}
  pos := fun _ => 0
  mid := fun _ j => (1 / 2 : ℂ) * hexUnit (2 * (j : ℤ))
  obs := fun _ => c
  relation := by
    intro v _
    have e2 : hexUnit (2 * ((1 : Fin 3) : ℤ)) = hexUnit 0 * hexOmega := by
      have hcast : (2 * ((1 : Fin 3) : ℤ)) = (0 : ℤ) + 2 := by decide
      rw [hcast]; exact hexFam_hexUnit_add_two 0
    have e4 : hexUnit (2 * ((2 : Fin 3) : ℤ)) = hexUnit 0 * hexOmega ^ 2 := by
      have h1 := hexFam_hexUnit_add_two 2
      have hcast : (2 * ((2 : Fin 3) : ℤ)) = (2 : ℤ) + 2 := by decide
      rw [hcast, h1, show hexUnit 2 = hexUnit 0 * hexOmega from by
            have h2 : (2 : ℤ) = 0 + 2 := by decide
            rw [h2]; exact hexFam_hexUnit_add_two 0]
      ring
    have e0 : hexUnit (2 * ((0 : Fin 3) : ℤ)) = hexUnit 0 := by norm_num
    rw [Fin.sum_univ_three, e0, e2, e4]
    have key : ((1 / 2 : ℂ) * hexUnit 0 - 0) * c
        + ((1 / 2 : ℂ) * (hexUnit 0 * hexOmega) - 0) * c
        + ((1 / 2 : ℂ) * (hexUnit 0 * hexOmega ^ 2) - 0) * c
        = (1 / 2 : ℂ) * hexUnit 0 * c * (1 + hexOmega + hexOmega ^ 2) := by ring
    rw [key, hexFam_omega_sum_zero, mul_zero]


end StatMech.Universality
