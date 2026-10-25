/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonGlobalReduction.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbol.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Def.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem anisotropicSquareKWSymbolMatrix_det
    (x y omega z₁ z₂ : Complex) (homega : omega ^ 2 = Complex.I)
    (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) :
    (anisotropicSquareKWSymbolMatrix x y omega z₁ z₂).det =
      (1 + x ^ 2) * (1 + y ^ 2) -
        x * (1 - y ^ 2) * (z₁ + z₁⁻¹) -
        y * (1 - x ^ 2) * (z₂ + z₂⁻¹) := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have homega4 : omega ^ 4 = -1 := by
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, homega, hI]
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, hI]
    ring
  rw [anisotropicSquareKWSymbolMatrix, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.succAbove]
  field_simp [hz₁, hz₂]
  ring_nf
  rw [homega4, homega]
  ring_nf
  rw [hI4, hI]
  ring


end StatMech.FrontierA
