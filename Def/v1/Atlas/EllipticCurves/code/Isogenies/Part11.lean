/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Squarefree.Basic
public import Structure.v1.Atlas.EllipticCurves.code.Isogenies.Part8

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace IsogenyStandardForm

variable {F : Type u} [Field F]

namespace WithCurveData

variable (α : WithCurveData F)

/-- Two rational-map triples are equivalent if all pairwise cross-products
`ψ_i^(1) ψ_j^(2) - ψ_j^(1) ψ_i^(2)` lie in the ideal `(f₁)`. -/
def RationalMapTriple.IsEquiv {k : Type u} [CommRing k]
    {f₁ f₂ : MvPolynomial (Fin 3) k}
    (t₁ t₂ : RationalMapTriple f₁ f₂) : Prop :=
  let I := Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k))
  t₁.ψ_x * t₂.ψ_y - t₂.ψ_x * t₁.ψ_y ∈ I ∧
  t₁.ψ_x * t₂.ψ_z - t₂.ψ_x * t₁.ψ_z ∈ I ∧
  t₁.ψ_y * t₂.ψ_z - t₂.ψ_y * t₁.ψ_z ∈ I

end WithCurveData
end IsogenyStandardForm
