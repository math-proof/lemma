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
import Structure.v1.Atlas.TensorCategories.code.BasicMonoidalDefs
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
