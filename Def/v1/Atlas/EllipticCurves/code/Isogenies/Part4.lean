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
import Structure.v1.Atlas.EllipticCurves.code.Isogenies.Part3
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace ProjectiveCurve

variable {k : Type u} [CommRing k]

/-- A rational map `φ` is regular at an affine `k`-point `P` if there is a
nonzero scalar `μ` in the function field such that all three coordinates `μ·φᵢ`
are regular at `P` and at least one is regular and nonzero there. -/
def RationalMap.IsRegularAt {f₁ f₂ : k[X][Y]} [IsDomain (CoordinateRing f₁)]
    (φ : RationalMap f₁ f₂) (P : AffinePoint f₁) : Prop :=
  ∃ (μ : FunctionField f₁), μ ≠ 0 ∧
    (μ * φ.φ₁).IsRegularAt P ∧
    (μ * φ.φ₂).IsRegularAt P ∧
    (μ * φ.φ₃).IsRegularAt P ∧
    ((μ * φ.φ₁).IsRegularNonzeroAt P ∨
     (μ * φ.φ₂).IsRegularNonzeroAt P ∨
     (μ * φ.φ₃).IsRegularNonzeroAt P)

/-- Field-valued version of `IsRegularNonzeroAt`: a function is regular and nonzero
at an `L`-point `P` if it equals `g/h` for `h(P) ≠ 0` and `g(P) ≠ 0`. -/
def FunctionField.IsRegularNonzeroAtOver {f₀ : k[X][Y]} {K : Type u}
    [Field K] [Algebra k K]
    (φ : FunctionField f₀) (P : AffinePointOver f₀ K) : Prop :=
  ∃ (g : CoordinateRing f₀) (h : ↥(nonZeroDivisors (CoordinateRing f₀))),
    φ = IsLocalization.mk' (FunctionField f₀) g h ∧
    P.evalRingHom (h : CoordinateRing f₀) ≠ 0 ∧
    P.evalRingHom g ≠ 0

/-- Field-valued regularity for rational maps: there exists a rescaling `μ` so that
each coordinate is regular at `P` and at least one is regular and nonzero. -/
def RationalMap.IsRegularAtOver {f₁ f₂ : k[X][Y]}
    [IsDomain (CoordinateRing f₁)]
    (φ : RationalMap f₁ f₂) {K : Type u} [Field K] [Algebra k K]
    (P : AffinePointOver f₁ K) : Prop :=
  ∃ (μ : FunctionField f₁), μ ≠ 0 ∧
    (μ * φ.φ₁).IsRegularAtOver P ∧
    (μ * φ.φ₂).IsRegularAtOver P ∧
    (μ * φ.φ₃).IsRegularAtOver P ∧
    ((μ * φ.φ₁).IsRegularNonzeroAtOver P ∨
     (μ * φ.φ₂).IsRegularNonzeroAtOver P ∨
     (μ * φ.φ₃).IsRegularNonzeroAtOver P)

end ProjectiveCurve
