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
import Theorem.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


def squareTorusDirectionWeight (x y : Complex) (mu : Fin 4) : Complex :=
  match mu with
  | 0 => x
  | 1 => y
  | 2 => x
  | 3 => y


noncomputable def anisotropicSquareKWMatrixPhase
    (L : Nat) (x y omega u v : Complex) :
    Matrix (ons_Dart L) (ons_Dart L) Complex :=
  fun d₂ d₁ =>
    ons_dirPhase u v d₁.2 *
      if d₂.1 = ons_dirStep L d₁.2 d₁.1 then
        squareTorusDirectionWeight x y d₁.2 * ons_turnW omega d₁.2 d₂.2
      else 0


noncomputable def anisotropicSquareKWSymbolMatrix
    (x y omega z₁ z₂ : Complex) : Matrix (Fin 4) (Fin 4) Complex :=
  !![1 - x * z₁, -y * (-Complex.I * omega) * z₂,
        0, -y * omega * z₂⁻¹;
     -x * omega * z₁, 1 - y * z₂,
        -x * (-Complex.I * omega) * z₁⁻¹, 0;
     0, -y * omega * z₂, 1 - x * z₁⁻¹,
        -y * (-Complex.I * omega) * z₂⁻¹;
     -x * (-Complex.I * omega) * z₁, 0,
        -x * omega * z₁⁻¹, 1 - y * z₂⁻¹]


end StatMech.FrontierA
