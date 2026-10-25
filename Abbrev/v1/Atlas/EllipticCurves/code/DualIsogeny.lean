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
open WeierstrassCurve.Affine


namespace DualIsogeny

variable {F : Type*} [Field F] [DecidableEq F]

variable {E₁ E₂ : WeierstrassCurve.Affine F}

/-- The dual isogeny `α̂ : E₂ → E₁` associated to an isogeny `α : E₁ → E₂`. -/
noncomputable abbrev dualIsogeny (α : Isogeny E₁ E₂) : Isogeny E₂ E₁ :=
  α.dualIsogeny

end DualIsogeny
