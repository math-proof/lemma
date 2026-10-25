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
import Def.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part3
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem anisotropicSquareKWSymbolMatrix_det_cos
    (x y k₁ k₂ : Real) :
    (anisotropicSquareKWSymbolMatrix (x : Complex) (y : Complex)
      ons_turnRoot
      (Complex.exp (Complex.I * k₁))
      (Complex.exp (Complex.I * k₂))).det =
        (anisotropicSquareHighTempSymbol x y k₁ k₂ : Complex) := by
  have hcos : ∀ k : Real,
      Complex.exp (Complex.I * (k : Complex)) +
          Complex.exp (-(Complex.I * (k : Complex))) =
        2 * (Real.cos k : Complex) := by
    intro k
    rw [Complex.ofReal_cos, Complex.two_cos,
      mul_comm Complex.I (k : Complex), neg_mul]
  rw [anisotropicSquareKWSymbolMatrix_det]
  · rw [show (Complex.exp (Complex.I * (k₁ : Complex)))⁻¹ =
        Complex.exp (-(Complex.I * (k₁ : Complex))) from
      (Complex.exp_neg _).symm]
    rw [show (Complex.exp (Complex.I * (k₂ : Complex)))⁻¹ =
        Complex.exp (-(Complex.I * (k₂ : Complex))) from
      (Complex.exp_neg _).symm]
    rw [hcos k₁, hcos k₂]
    push_cast
    rw [← Complex.ofReal_cos, ← Complex.ofReal_cos]
    unfold anisotropicSquareHighTempSymbol
    norm_cast
    ring
  · exact ons_turnRoot_sq
  · exact Complex.exp_ne_zero _
  · exact Complex.exp_ne_zero _

end StatMech.FrontierA
