/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TensorProductDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.FiniteStability
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

open TensorProduct
set_option autoImplicit false

class IsAffineAlgebra (k : Type*) (R : Type*) [Field k] [CommRing R] [Algebra k R] : Prop where
  isDomain : IsDomain R
  finiteType : Algebra.FiniteType k R


attribute [instance] IsAffineAlgebra.isDomain IsAffineAlgebra.finiteType

section Helpers

variable {k : Type*} [Field k] [IsAlgClosed k]
  {R : Type*} [CommRing R] [Algebra k R] [IsDomain R] [Algebra.FiniteType k R]
  {S : Type*} [CommRing S] [Algebra k S] [IsDomain S]

noncomputable def algHomOfMaximalIdeal (k : Type*) {R : Type*}
    [Field k] [IsAlgClosed k] [CommRing R] [Algebra k R] [IsDomain R] [Algebra.FiniteType k R]
    (m : Ideal R) [hm : m.IsMaximal] : R →ₐ[k] k := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (R ⧸ m) := Algebra.FiniteType.quotient k m
  haveI : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ m)
  haveI : Algebra.IsIntegral k (R ⧸ m) := Algebra.IsIntegral.of_finite k (R ⧸ m)
  exact (AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := R ⧸ m))).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom k R (R ⧸ m))

noncomputable def evalTensorMap (φ : R →ₐ[k] k) : R ⊗[k] S →ₐ[k] S :=
  Algebra.TensorProduct.productMap ((Algebra.ofId k S).comp φ) (AlgHom.id k S)
