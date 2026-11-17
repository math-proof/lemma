module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/TensorProductDomain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.TensorProduct.Nontrivial
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public section

open TensorProduct
set_option autoImplicit false


class IsAffineAlgebra (k : Type*) (R : Type*) [Field k] [CommRing R] [Algebra k R] : Prop where
  isDomain : IsDomain R
  finiteType : Algebra.FiniteType k R


