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
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part10
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace IsogenyStandardForm

variable {F : Type u} [Field F]

namespace WithCurveData

variable (α : WithCurveData F)

/-- A rational map from the projective curve `f₁ = 0` to `f₂ = 0`, represented by
a homogeneous triple whose components are not all in the ideal `(f₁)`, and which
satisfies `f₂(ψ_x, ψ_y, ψ_z) ∈ (f₁)` (so the image lies on `f₂`). -/
structure RationalMapTriple {k : Type u} [CommRing k]
    (f₁ f₂ : MvPolynomial (Fin 3) k) extends HomogeneousTriple k where
  not_all_in_ideal :
    ψ_x ∉ Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k)) ∨
    ψ_y ∉ Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k)) ∨
    ψ_z ∉ Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k))
  image_in_ideal :
    toHomogeneousTriple.substIn f₂ ∈ Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k))

end WithCurveData
end IsogenyStandardForm
