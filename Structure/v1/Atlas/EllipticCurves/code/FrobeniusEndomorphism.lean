/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Frobenius
open Polynomial

universe u


namespace FrobeniusEndomorphism

variable {F : Type u} [Field F]

/-- A ring homomorphism $\varphi : F \to F$ *fixes the coefficients* of a Weierstrass
curve $W$ if it acts as the identity on the five defining coefficients $a_1, a_2, a_3,
a_4, a_6$. This is the condition needed for $\varphi$ to descend to a map of curves. -/
structure FixesCoeffs (W : WeierstrassCurve.Affine F) (φ : F →+* F) : Prop where
  fix_a₁ : φ W.a₁ = W.a₁
  fix_a₂ : φ W.a₂ = W.a₂
  fix_a₃ : φ W.a₃ = W.a₃
  fix_a₄ : φ W.a₄ = W.a₄
  fix_a₆ : φ W.a₆ = W.a₆

end FrobeniusEndomorphism
