/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutMultiplicitySum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutLight
import Mathlib.RingTheory.Localization.AtPrime.Basic


noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- The projective intersection number of two homogeneous polynomials `f, g` in three variables,
defined as the `k`-dimension of the degree-`n` piece of `k[x,y,z] / (⟨f⟩ + ⟨g⟩)`. -/
noncomputable def projectiveIntersectionNumber
    (f g : MvPolynomial (Fin 3) k) (n : ℕ) : ℕ :=
  Module.finrank k (homogQuotPiece k (Ideal.span {f} ⊔ Ideal.span {g}) n)

end
