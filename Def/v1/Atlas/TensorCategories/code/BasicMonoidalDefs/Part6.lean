/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasicMonoidalDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

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
public import Class.v1.Atlas.TensorCategories.code.BasicMonoidalDefs

@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category


attribute [instance] endofunctorMonoidalCategory

universe v₁ v₂ u₁ u₂


namespace TensorCategories

section Section_1_2

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

section Section_1_8

/-- Example 1.8.2: the category of endofunctors `C ⥤ C` of any category is monoidal
under composition, and that monoidal structure is strict. -/
@[reducible]
def ex_1_8_2_endofunctor_monoidal (C : Type u₁) [Category.{v₁} C] :
    MonoidalCategory (C ⥤ C) :=
  endofunctorMonoidalCategory C

end Section_1_8


section Section_1_9

/-- Theorem 1.9 (Mac Lane normalization): the identity on the free monoidal category on
`C` is naturally isomorphic to the composition `fullNormalize ⋙ inclusion`. -/
def thm_1_9_normalization (C : Type*) :
    𝟭 (FreeMonoidalCategory C) ≅
    FreeMonoidalCategory.fullNormalize C ⋙ FreeMonoidalCategory.inclusion :=
  FreeMonoidalCategory.fullNormalizeIso C

end Section_1_9
end Section_1_2
end TensorCategories
