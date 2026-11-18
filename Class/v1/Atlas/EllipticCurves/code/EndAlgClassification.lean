module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/EndAlgClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Quaternion
public import Mathlib.Algebra.QuaternionBasis
public import Instance.v1.Atlas.EllipticCurves.code.EndAlgebra.Part5
public import Instance.v1.Atlas.EllipticCurves.code.EndomorphismAlgebra.Part2
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.SimpleRing.Basic
public section
open Module
open scoped Quaternion TensorProduct

/-- A `ℚ`-algebra `A` equipped with an anti-involution `invol` together with a positive-definite
reduced norm `normMap : A → ℚ` satisfying `a * invol a = normMap a`. This abstracts the structure
of the Rosati involution on the endomorphism algebra of an abelian variety. -/
class PositiveDefiniteInvolutionAlgebra (A : Type*) [Ring A] [Algebra ℚ A] where
  invol : A → A
  invol_invol : ∀ a : A, invol (invol a) = a
  invol_add : ∀ a b : A, invol (a + b) = invol a + invol b
  invol_mul : ∀ a b : A, invol (a * b) = invol b * invol a
  invol_one : invol 1 = 1
  invol_rat : ∀ q : ℚ, invol ((algebraMap ℚ A) q) = (algebraMap ℚ A) q
  normMap : A → ℚ
  normMap_spec : ∀ a : A, a * invol a = (algebraMap ℚ A) (normMap a)
  normMap_pos : ∀ a : A, a ≠ 0 → 0 < normMap a

