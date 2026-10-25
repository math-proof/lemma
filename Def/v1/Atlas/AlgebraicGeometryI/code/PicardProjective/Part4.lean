/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Theorem.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part3


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- The degree map Pic(P^n) → ℤ defined on equivalence classes. -/
def GradedPicardGroup.degreeMap (σ : Type*) (k : Type*) [Field k] :
    GradedPicardGroup σ k → ℤ :=
  Quotient.lift (HomogFraction.degree σ k) (degree_compat σ k)


/-- Multiplication of homogeneous fractions: corresponds to tensor product of twists
in Pic(P^n). -/
def HomogFraction.mul (σ : Type*) (k : Type*) [Field k]
    (p q : HomogFraction σ k) : HomogFraction σ k where
  num := p.num * q.num
  den := p.den * q.den
  num_ne := mul_ne_zero p.num_ne q.num_ne
  den_ne := mul_ne_zero p.den_ne q.den_ne
  ndeg := p.ndeg + q.ndeg
  ddeg := p.ddeg + q.ddeg
  nhom := p.nhom.mul q.nhom
  dhom := p.dhom.mul q.dhom

/-- The trivial homogeneous fraction 1/1, representing the structure sheaf O_{P^n}. -/
def HomogFraction.one (σ : Type*) (k : Type*) [Field k] : HomogFraction σ k where
  num := 1
  den := 1
  num_ne := one_ne_zero
  den_ne := one_ne_zero
  ndeg := 0
  ddeg := 0
  nhom := isHomogeneous_one σ k
  dhom := isHomogeneous_one σ k

/-- Inverse of a homogeneous fraction: swap numerator and denominator, corresponding
to the dual line bundle. -/
def HomogFraction.inv (σ : Type*) (k : Type*) [Field k]
    (p : HomogFraction σ k) : HomogFraction σ k where
  num := p.den
  den := p.num
  num_ne := p.den_ne
  den_ne := p.num_ne
  ndeg := p.ddeg
  ddeg := p.ndeg
  nhom := p.dhom
  dhom := p.nhom

end PicardProjective
end
