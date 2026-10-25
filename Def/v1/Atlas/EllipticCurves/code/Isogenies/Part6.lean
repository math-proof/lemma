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
import Structure.v1.Atlas.EllipticCurves.code.Isogenies.Part4
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace ProjectiveCurve

variable {k : Type u} [CommRing k]

/-- Partial derivative with respect to `Y` of a bivariate polynomial in `k[X][Y]`,
implemented as the formal derivative in the outer (Y) variable. -/
noncomputable def partialDerivY (f₀ : k[X][Y]) : k[X][Y] :=
  Polynomial.derivative f₀

/-- Partial derivative with respect to `X` of a bivariate polynomial in `k[X][Y]`,
obtained by differentiating each coefficient. -/
noncomputable def partialDerivX (f₀ : k[X][Y]) : k[X][Y] :=
  f₀.sum fun n c => Polynomial.C (Polynomial.derivative c) * Polynomial.X ^ n

/-- A plane curve `f₀ = 0` is *smooth* if at every affine `k`-point at least one
of the two partial derivatives is nonzero. -/
def IsSmooth (f₀ : k[X][Y]) : Prop :=
  ∀ P : AffinePoint f₀,
    Polynomial.eval₂ (Polynomial.evalRingHom P.x) P.y (partialDerivX f₀) ≠ 0 ∨
    Polynomial.eval₂ (Polynomial.evalRingHom P.x) P.y (partialDerivY f₀) ≠ 0

/-- Every rational map out of a smooth plane curve extends to a morphism: this is
the curve-theoretic fact that a rational map from a smooth curve is automatically
regular at every point. -/

section MorphismSurjectiveOrConstant

variable {k : Type u} [Field k] {f₁ f₂ : k[X][Y]} [IsDomain (CoordinateRing f₁)]

/-- A morphism `φ` maps an affine point `P` of the source to an affine point `Q`
of the target if the three coordinate ratios can be rescaled to send `P` to `Q`. -/
def Morphism.MapsTo (φ : Morphism f₁ f₂) (P : AffinePoint f₁) (Q : AffinePoint f₂) : Prop :=
  ∃ (μ : FunctionField f₁) (_ : μ ≠ 0)
    (g₁ : CoordinateRing f₁) (h₁ : ↥(nonZeroDivisors (CoordinateRing f₁)))
    (g₂ : CoordinateRing f₁) (h₂ : ↥(nonZeroDivisors (CoordinateRing f₁)))
    (g₃ : CoordinateRing f₁) (h₃ : ↥(nonZeroDivisors (CoordinateRing f₁))),
    μ * φ.φ₁ = IsLocalization.mk' (FunctionField f₁) g₁ h₁ ∧
    μ * φ.φ₂ = IsLocalization.mk' (FunctionField f₁) g₂ h₂ ∧
    μ * φ.φ₃ = IsLocalization.mk' (FunctionField f₁) g₃ h₃ ∧
    P.evalRingHom (h₁ : CoordinateRing f₁) ≠ 0 ∧
    P.evalRingHom (h₂ : CoordinateRing f₁) ≠ 0 ∧
    P.evalRingHom (h₃ : CoordinateRing f₁) ≠ 0 ∧
    P.evalRingHom g₃ ≠ 0 ∧
    Q.x * (P.evalRingHom (h₁ : CoordinateRing f₁) * P.evalRingHom g₃) =
      P.evalRingHom g₁ * P.evalRingHom (h₃ : CoordinateRing f₁) ∧
    Q.y * (P.evalRingHom (h₂ : CoordinateRing f₁) * P.evalRingHom g₃) =
      P.evalRingHom g₂ * P.evalRingHom (h₃ : CoordinateRing f₁)

/-- A morphism is surjective on affine `k`-points if every target affine point has
at least one preimage. -/
def Morphism.IsSurjective (φ : Morphism f₁ f₂) : Prop :=
  ∀ Q : AffinePoint f₂, ∃ P : AffinePoint f₁, φ.MapsTo P Q

/-- A morphism is constant if there is a single target point that every source
point is mapped to. -/
def Morphism.IsConstant (φ : Morphism f₁ f₂) : Prop :=
  ∃ Q₀ : AffinePoint f₂, ∀ P : AffinePoint f₁, φ.MapsTo P Q₀

end MorphismSurjectiveOrConstant

/-- Dichotomy for morphisms between plane curves over a field: a morphism is either
surjective on affine `k`-points or constant. -/

section RationalMapNonConstant

variable {k : Type u} [Field k] {f₁ f₂ : k[X][Y]} [IsDomain (CoordinateRing f₁)]

/-- A rational map `φ` is non-constant if the affine ratios `φ₁/φ₃` and `φ₂/φ₃` do
not both lie in the image of the constant map `k → k(f₁)`. -/
def RationalMap.IsNonConstant (φ : RationalMap f₁ f₂) : Prop :=
  ¬ ∃ (a b : k), φ.φ₁ / φ.φ₃ = algebraMap k (FunctionField f₁) a ∧
                  φ.φ₂ / φ.φ₃ = algebraMap k (FunctionField f₁) b

end RationalMapNonConstant
end ProjectiveCurve
