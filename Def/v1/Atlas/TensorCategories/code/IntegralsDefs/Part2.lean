/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.SimpleModule.Basic
public import Instance.v1.Atlas.TensorCategories.code.DistinguishedInvertible.Part2
public import Theorem.Category.Atlas.v1.TensorCategories.code.DistinguishedInvertible
public import Structure.v1.Atlas.TensorCategories.code.IntegralsDefs.Part2
@[expose] public section
set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra
open scoped TensorProduct

universe u v w


section Prop1525

variable {R : Type u} [CommSemiring R] {H : Type v} [Semiring H] [Algebra R H] [Coalgebra R H]

/-- An algebra is unimodular when every left integral is also a right integral
(Definition 1.52.6 at the algebra level). -/
def IsUnimodularAlgebra : Prop :=
  ∀ (I : H), IsLeftIntegral R H I → IsRightIntegral R H I

end Prop1525
