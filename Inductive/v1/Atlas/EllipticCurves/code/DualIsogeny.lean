/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/DualIsogeny.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.TorsionEndomorphism.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.TorsionEndomorphism
import Lemma.Complex.Atlas.v1.EllipticCurves.code.DivisionPolynomials
import Def.v1.Atlas.EllipticCurves.code.DivisionPolynomials.Part10
import Abbrev.v1.Atlas.EllipticCurves.code.DualIsogeny
open WeierstrassCurve.Affine


namespace DualIsogeny

variable {F : Type*} [Field F] [DecidableEq F]

variable {E₁ E₂ : WeierstrassCurve.Affine F}

/-- An isogeny `E₁ → E₂` or the zero map (which is not an isogeny, but is needed to make
the set of "isogenies-or-zero" into a monoid). -/
inductive IsogenyOrZero (E₁ E₂ : WeierstrassCurve.Affine F) where
  | zero : IsogenyOrZero E₁ E₂
  | ofIsogeny (α : Isogeny E₁ E₂) : IsogenyOrZero E₁ E₂

end DualIsogeny
