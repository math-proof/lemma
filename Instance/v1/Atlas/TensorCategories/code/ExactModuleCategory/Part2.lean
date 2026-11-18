/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
public import Abbrev.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Noetherian
public import Mathlib.RingTheory.Finiteness.Defs
public import Class.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part2

@[expose] public section

set_option maxHeartbeats 400000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

namespace ExactModuleCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]

namespace QuasiFrobeniusProperty

variable {A : Type*} [Category A] [QuasiFrobeniusProperty A]

/-- In a quasi-Frobenius category, every projective object is injective. -/
instance projective_injective (X : A) [Projective X] : Injective X :=
  projective_is_injective X

/-- In a quasi-Frobenius category, every injective object is projective. -/
instance injective_projective (X : A) [Injective X] : Projective X :=
  injective_is_projective X

end QuasiFrobeniusProperty
end ExactModuleCategory
end CategoryTheory
