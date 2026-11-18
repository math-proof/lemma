module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Class.v1.Atlas.TensorCategories.code.ExactModuleCategory
public section
set_option maxHeartbeats 400000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

namespace ExactModuleCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]

/-- In the finite abelian setting, whiskering an epi on the right by an object of the
module category yields an epi. -/
class QuasiFrobeniusProperty (A : Type*) [Category A] : Prop where
  projective_is_injective : ∀ (X : A), [Projective X] → Injective X
  injective_is_projective : ∀ (X : A), [Injective X] → Projective X

end ExactModuleCategory
end CategoryTheory
