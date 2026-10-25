/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasicMonoidalDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Monoidal.Free.Coherence
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Equivalence
import Mathlib.RingTheory.Finiteness.Basic
import Class.v1.Atlas.TensorCategories.code.BasicMonoidalDefs
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
