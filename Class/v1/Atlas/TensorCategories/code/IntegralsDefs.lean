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
import Def.v1.Atlas.TensorCategories.code.IntegralsDefs
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
  integral_isLeftIntegral : IsLeftIntegral k H integral
  integral_ne_zero : integral ≠ 0
  integral_unique : ∀ (J : H), IsLeftIntegral k H J → ∃ (c : k), J = c • integral

/-- Typeclass packaging the existence of a distinguished, essentially unique nonzero
right integral in `H`. -/
class HasUniqueRightIntegral where
  integral : H
  integral_isRightIntegral : IsRightIntegral k H integral
  integral_ne_zero : integral ≠ 0
  integral_unique : ∀ (J : H), IsRightIntegral k H J → ∃ (c : k), J = c • integral

end IntegralDefs
