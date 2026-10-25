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


