/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Smooth.Basic


noncomputable section

open scoped TensorProduct

open Polynomial KaehlerDifferential Module

universe u v

section UniversalProperty

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- The explicit S-linear equivalence `(Ω[S⁄R] →ₗ[S] M) ≃ₗ[S] Der R S M` witnessing the
universal property of Kähler differentials. -/
def kaehlerDifferentialEquivDerivation
    {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    (Ω[S⁄R] →ₗ[S] M) ≃ₗ[S] Derivation R S M :=
  KaehlerDifferential.linearMapEquivDerivation R S

/-- For the polynomial algebra `k[X]`, the Kähler differentials are a free rank-one
module: `Ω[k[X]⁄k] ≃ₗ[k[X]] k[X]`, with `dX` corresponding to `1`. -/
def kaehlerDifferential_polynomial_equiv :
    Ω[Polynomial k⁄k] ≃ₗ[Polynomial k] Polynomial k :=
  KaehlerDifferential.polynomialEquiv k

/-- Canonical basis `{dXᵢ}ᵢ` of `Ω[k[σ]⁄k]` as a free `k[σ]`-module indexed by `σ`. -/
def kaehlerDifferential_mvPolynomial_basis (σ : Type*) :
    Basis σ (MvPolynomial σ k) (Ω[MvPolynomial σ k⁄k]) :=
  KaehlerDifferential.mvPolynomialBasis k σ

end UniversalProperty
end
