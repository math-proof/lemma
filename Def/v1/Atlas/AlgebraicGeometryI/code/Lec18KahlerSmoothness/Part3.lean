/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec18KahlerSmoothness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec18KahlerSmoothness

@[expose] public section

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 400000


noncomputable section

open IsLocalRing

/-- The Jacobian matrix `(∂f_i/∂x_j)(x)` of a family of polynomials `f_1,…,f_m` evaluated
at the point `x ∈ k^n`. -/
def jacobianMatrix {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) (x : Fin n → k) :
    Matrix (Fin m) (Fin n) k :=
  fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (f i))

/-- Definition 34 (Lecture 18). The universal property characterising Kähler differentials:
`A`-linear maps `Ω[A⁄k] → M` correspond naturally to `k`-derivations `A → M`. -/
def Definition34_KaehlerDifferential_universalProperty
    (k : Type*) (A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] :
    (Ω[A⁄k] →ₗ[A] M) ≃ₗ[A] Derivation k A M :=
  KaehlerDifferential.linearMapEquivDerivation k A

/-- Definition 35 (Lecture 18). The Zariski cotangent space of a local ring `R`, defined as
`m/m²` viewed as a vector space over the residue field. -/
def Definition35_CotangentSpace
    (R : Type*) [CommRing R] [IsLocalRing R] :=
  IsLocalRing.CotangentSpace R

end
