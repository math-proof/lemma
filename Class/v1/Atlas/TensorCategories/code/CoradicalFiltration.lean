module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoradicalFiltration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Abbrev.v1.Atlas.TensorCategories.code.CoalgebraBialgebra.Part4
public import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
public import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Simple
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.RingTheory.Coalgebra.Hom
public import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part2
public section
set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra

universe u v

variable {R : Type u} {C : Type v}
variable [CommRing R] [AddCommGroup C] [Module R C] [Coalgebra R C]

namespace Submodule

/-- A locally finite-length category: each non-simple non-zero object admits a short exact
sequence with simple quotient and a strictly shorter subobject. -/
class IsLocallyFiniteLength (𝒞 : Type*) [CategoryTheory.Category 𝒞]
    [CategoryTheory.Abelian 𝒞] where
  length : 𝒞 → ℕ
  exists_ses_simple_quotient : ∀ (Y : 𝒞),
    ¬ CategoryTheory.Limits.IsZero Y → ¬ CategoryTheory.Simple Y →
    ∃ (S : CategoryTheory.ShortComplex 𝒞), S.ShortExact ∧ S.X₂ = Y ∧
      CategoryTheory.Simple S.X₃ ∧ length S.X₁ < length Y

end Submodule
