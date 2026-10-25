/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Squarefree.Basic
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part12
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace IsogenyStandardForm

variable {F : Type u} [Field F]

namespace Isogeny

variable {F : Type u} [Field F] [DecidableEq F]

variable {E₁ E₂ : WeierstrassCurve.Affine F}

open Polynomial

/-- A *representation* of an isogeny `α : E₁ → E₂` in standard form: it records
`(u, v, s, t) ∈ F[X]` and the fact that on a nonsingular point `(x₀, y₀)` with
`v(x₀) ≠ 0`, `α` sends `(x₀, y₀) ↦ (u(x₀)/v(x₀), (s(x₀)/t(x₀))·y₀)`; in the
"pole" case `v(x₀) = 0` and `u(x₀) ≠ 0`, the image is the identity. -/
structure IsogenyRepresentation (E₁ E₂ : WeierstrassCurve.Affine F)
    (α : Isogeny E₁ E₂) extends IsogenyStandardForm F where
  represents : ∀ (x₀ y₀ : F) (h₁ : E₁.Nonsingular x₀ y₀)
    (_hv : eval x₀ v ≠ 0),
    ∃ (h₂ : E₂.Nonsingular (eval x₀ u / eval x₀ v)
                             (eval x₀ s / eval x₀ t * y₀)),
    α.toAddMonoidHom (WeierstrassCurve.Affine.Point.some x₀ y₀ h₁) =
      WeierstrassCurve.Affine.Point.some
        (eval x₀ u / eval x₀ v)
        (eval x₀ s / eval x₀ t * y₀) h₂
  maps_poles_to_zero : ∀ (x₀ y₀ : F) (h₁ : E₁.Nonsingular x₀ y₀)
    (_hv : eval x₀ v = 0) (_hu : eval x₀ u ≠ 0),
    α.toAddMonoidHom (WeierstrassCurve.Affine.Point.some x₀ y₀ h₁) = 0

end Isogeny
end IsogenyStandardForm
