/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DualIsogeny.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.EllipticCurves.code.TorsionEndomorphism
import Lemma.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
import Lemma.Complex.Atlas.v1.EllipticCurves.code.DivisionPolynomials
import sympy.atlas.v1.Atlas.EllipticCurves.code.DivisionPolynomials

open WeierstrassCurve.Affine

namespace DualIsogeny

variable {F : Type*} [Field F] [DecidableEq F]
variable {E₁ E₂ : WeierstrassCurve.Affine F}

/-- The dual isogeny `α̂ : E₂ → E₁` associated to an isogeny `α : E₁ → E₂`. -/
noncomputable abbrev dualIsogeny (α : Isogeny E₁ E₂) : Isogeny E₂ E₁ :=
  α.dualIsogeny

/-- An isogeny `E₁ → E₂` or the zero map (which is not an isogeny, but is needed to make
the set of "isogenies-or-zero" into a monoid). -/
inductive IsogenyOrZero (E₁ E₂ : WeierstrassCurve.Affine F) where
  | zero : IsogenyOrZero E₁ E₂
  | ofIsogeny (α : Isogeny E₁ E₂) : IsogenyOrZero E₁ E₂

/-- Converts an `IsogenyOrZero` to the underlying additive group homomorphism. -/
def IsogenyOrZero.toAddMonoidHom : IsogenyOrZero E₁ E₂ → (E₁.Point →+ E₂.Point)
  | .zero => 0
  | .ofIsogeny α => α.toAddMonoidHom

/-- The degree of an `IsogenyOrZero` (zero for the zero map, the degree of the isogeny otherwise). -/
def IsogenyOrZero.deg : IsogenyOrZero E₁ E₂ → ℕ
  | .zero => 0
  | .ofIsogeny α => α.degree

/-- The dual of an `IsogenyOrZero`: zero stays zero, an isogeny is sent to its dual. -/
noncomputable def IsogenyOrZero.dual : IsogenyOrZero E₁ E₂ → IsogenyOrZero E₂ E₁
  | .zero => .zero
  | .ofIsogeny α => .ofIsogeny α.dualIsogeny
