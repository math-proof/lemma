module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Def.v1.Atlas.TensorCategories.code.IntegralsDefs
public section
set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra
open scoped TensorProduct

universe u v w

section IntegralDefs

variable (R : Type u) [CommSemiring R] (H : Type v) [Semiring H] [Algebra R H] [Coalgebra R H]

/-- Frobenius theorem applied to integrals: the space of left integrals in a finite
dimensional quasi-Hopf algebra has dimension `1`. -/
class HasUniqueLeftIntegral where
  integral : H
  integral_isLeftIntegral : IsLeftIntegral R H integral
  integral_ne_zero : integral ≠ 0
  integral_unique : ∀ (J : H), IsLeftIntegral R H J → ∃ (c : R), J = c • integral

/-- Typeclass packaging the existence of a distinguished, essentially unique nonzero
right integral in `H`. -/
class HasUniqueRightIntegral where
  integral : H
  integral_isRightIntegral : IsRightIntegral R H integral
  integral_ne_zero : integral ≠ 0
  integral_unique : ∀ (J : H), IsRightIntegral R H J → ∃ (c : R), J = c • integral

end IntegralDefs
