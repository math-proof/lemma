module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasicMonoidalDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Monoidal.Free.Coherence
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Monoidal.End
public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.RingTheory.Finiteness.Basic
public import Def.v1.Atlas.TensorCategories.code.BasicMonoidalDefs.Part5
public section
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category


attribute [instance] endofunctorMonoidalCategory

universe v₁ v₂ u₁ u₂


namespace TensorCategories

section Section_1_2

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

section Section_1_8

/-- A monoidal category is strict if the associator and unitors are identities on the
nose: `(X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)`, `𝟙_ C ⊗ X = X`, and `X ⊗ 𝟙_ C = X`. -/
class IsStrictMonoidal (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] : Prop where
  assoc_strict : ∀ X Y Z : C, (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z)
  left_unit_strict : ∀ X : C, 𝟙_ C ⊗ X = X
  right_unit_strict : ∀ X : C, X ⊗ 𝟙_ C = X

end Section_1_8
end Section_1_2
end TensorCategories
