/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.SimpleModule.Basic
import Instance.v1.Atlas.TensorCategories.code.DistinguishedInvertible.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.DistinguishedInvertible
import Class.v1.Atlas.TensorCategories.code.IntegralsDefs
set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra
open scoped TensorProduct

universe u v w


section Prop1525

variable {R : Type u} [CommSemiring R] {H : Type v} [Semiring H] [Algebra R H] [Coalgebra R H]

/-- The distinguished character `χ : H →ₗ[R] R` associated to a left integral `I`,
characterized by the right multiplication law `I * x = χ(x) • I`. -/
structure DistinguishedCharacter (I : H) where
  χ : H →ₗ[R] R
  left_int : IsLeftIntegral R H I
  right_law : ∀ (x : H), I * x = χ x • I

end Prop1525
