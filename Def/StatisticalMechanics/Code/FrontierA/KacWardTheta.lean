/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTheta.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCactusAssembly.Part2
import Mathlib.LinearAlgebra.Matrix.SchurComplement
open scoped BigOperators


namespace StatMech.FrontierA

open Matrix StatMech.Onsager


def kwThetaLeftDirection : Fin 3 -> Fin 4 := ![1, 0, 3]


def kwThetaRightDirection : Fin 3 -> Fin 4 := ![1, 2, 3]


noncomputable def kwThetaForwardInternal (omega : ℂ) : Fin 3 -> ℂ :=
  ![(omega⁻¹) ^ 2, 1, omega ^ 2]


noncomputable def kwThetaReverseInternal (omega : ℂ) : Fin 3 -> ℂ :=
  ![omega ^ 2, 1, (omega⁻¹) ^ 2]


noncomputable def kwThetaForward (omega : ℂ) (x : Fin 3 -> ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i = j then 0 else
    x i * kwThetaForwardInternal omega i *
      ons_turnW omega (kwThetaRightDirection i + 2) (kwThetaRightDirection j)


noncomputable def kwThetaReverse (omega : ℂ) (x : Fin 3 -> ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i = j then 0 else
    x i * kwThetaReverseInternal omega i *
      ons_turnW omega (kwThetaLeftDirection i + 2) (kwThetaLeftDirection j)


noncomputable def kwThetaTransition (omega : ℂ) (x : Fin 3 -> ℂ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ :=
  Matrix.fromBlocks 0 (kwThetaForward omega x) (kwThetaReverse omega x) 0


noncomputable def kwThetaEvenPolynomial (x : Fin 3 -> ℂ) : ℂ :=
  1 + x 0 * x 1 + x 0 * x 2 + x 1 * x 2

end StatMech.FrontierA
