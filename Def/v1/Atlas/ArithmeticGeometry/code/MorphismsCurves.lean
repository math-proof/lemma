/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/MorphismsCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Class.v1.Atlas.ArithmeticGeometry.code.MorphismsCurves


noncomputable section

open Module AlgebraicGeometry

universe u

namespace ArithmeticGeometry

attribute [instance] Curve_k.isIntegral Curve_k.isProper Curve_k.isSmooth

namespace FunctionField_k

variable {k : Type*} [Field k]

variable {F₁ : Type*} {F₂ : Type*} [Field F₁] [Field F₂]

/-- The degree of a morphism of function fields $\varphi : F_2 \to F_1$: the degree $[F_1 : \varphi(F_2)]$ of $F_1$ over the image. -/
def Morphism.degree (φ : F₂ →+* F₁) : ℕ :=
  Module.finrank φ.fieldRange F₁


end FunctionField_k
end ArithmeticGeometry
end
