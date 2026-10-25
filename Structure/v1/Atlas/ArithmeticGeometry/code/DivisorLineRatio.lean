/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/DivisorLineRatio.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Divisors.Part11
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Divisors


noncomputable section

open CurveDivisor

structure EllipticCurveP2Data (C : Type*) (F : Type*) [Field F] where
  curveInst : FunctionFieldCurve C F
  Line : Type*
  lineIntersectionDivisor : Line → CurveDivisor C
  linearFormRatio : Line → Line → Fˣ
  restrictLinearForm : Line → Fˣ
  ratio_eq_mul_inv : ∀ (L₁ L₂ : Line),
    linearFormRatio L₁ L₂ = restrictLinearForm L₁ * (restrictLinearForm L₂)⁻¹

end
