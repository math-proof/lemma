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
public import Structure.v1.Atlas.TensorCategories.code.BasicMonoidalDefs

@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category


attribute [instance] endofunctorMonoidalCategory

universe v₁ v₂ u₁ u₂


namespace TensorCategories

section Section_1_1

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

attribute [instance] Definition_1_1_2_MonoidalSubcategory.instCat
  Definition_1_1_2_MonoidalSubcategory.instMonoidal
  Definition_1_1_2_MonoidalSubcategory.instFaithful

/-- A full subcategory cut out by a monoidal object-property of `C` gives a monoidal
subcategory in the sense of `Definition_1_1_2_MonoidalSubcategory`. -/
def Definition_1_1_2_MonoidalSubcategory.ofFullSubcategory
    (P : ObjectProperty C) [P.IsMonoidal] :
    Definition_1_1_2_MonoidalSubcategory.{v₁, v₁, u₁, u₁} C where
  D := P.FullSubcategory
  ι := P.ι
  instMonoidalFunctor := inferInstance

end Section_1_1
end TensorCategories
