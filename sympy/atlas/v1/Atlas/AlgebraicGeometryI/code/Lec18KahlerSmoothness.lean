/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec18KahlerSmoothness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Maps

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 400000

noncomputable section

open IsLocalRing

/-- The maximal ideal `m_x ⊂ k[x_1,…,x_n]` of polynomials vanishing at the point `x ∈ k^n`,
defined as the kernel of evaluation at `x`. -/
def maxIdealOfPoint {k : Type*} [Field k] {n : ℕ}
    (x : Fin n → k) : Ideal (MvPolynomial (Fin n) k) :=
  RingHom.ker (MvPolynomial.eval x)

/-- The vanishing ideal of a point `x ∈ k^n` is maximal, since the evaluation map is
surjective onto the field `k`. -/
instance maxIdealOfPoint_isMaximal {k : Type*} [Field k] {n : ℕ}
    (x : Fin n → k) : (maxIdealOfPoint x).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (fun c => ⟨MvPolynomial.C c, MvPolynomial.eval_C c⟩)

/-- The image of `m_x` in the quotient `k[x_1,…,x_n]/I`, well-defined whenever `I ⊆ m_x`;
this is the maximal ideal of `x` viewed as a point of the affine variety `V(I)`. -/
def maxIdealOfPointInQuotient {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (_ : I ≤ maxIdealOfPoint x) :
    Ideal (MvPolynomial (Fin n) k ⧸ I) :=
  Ideal.map (Ideal.Quotient.mk I) (maxIdealOfPoint x)

/-- The image of `m_x` in `k[x_1,…,x_n]/I` is maximal. -/
instance maxIdealOfPointInQuotient_isMaximal {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint x) :
    (maxIdealOfPointInQuotient I x hI).IsMaximal := by
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le
  · exact Ideal.Quotient.mk_surjective
  · rwa [Ideal.mk_ker]

/-- The image of `m_x` in `k[x_1,…,x_n]/I` is prime (since maximal ideals are prime). -/
instance maxIdealOfPointInQuotient_isPrime {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint x) :
    (maxIdealOfPointInQuotient I x hI).IsPrime :=
  (maxIdealOfPointInQuotient_isMaximal I x hI).isPrime

/-- The local ring of the affine variety `V(I)` at the point `x`, obtained as the
localization of `k[x_1,…,x_n]/I` at the maximal ideal of `x`. -/
abbrev localRingAtPoint {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint x) :=
  Localization.AtPrime (maxIdealOfPointInQuotient I x hI)

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
