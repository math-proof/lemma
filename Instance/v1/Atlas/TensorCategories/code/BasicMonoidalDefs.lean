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
import Structure.v1.Atlas.TensorCategories.code.BasicMonoidalDefs.Part3
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category


attribute [instance] endofunctorMonoidalCategory

universe v₁ v₂ u₁ u₂


namespace TensorCategories

section Section_1_2

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

section Section_1_5

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

attribute [instance] def_1_4_5_MonoidalNatIso.isMonoidal

/-- The inverse component of a monoidal natural isomorphism is again a monoidal natural
transformation. -/
instance def_1_4_5_MonoidalNatIso.inv_isMonoidal
    {F₁ F₂ : C ⥤ D} [F₁.LaxMonoidal] [F₂.LaxMonoidal]
    (η : def_1_4_5_MonoidalNatIso F₁ F₂) : NatTrans.IsMonoidal η.toNatIso.inv :=
  inferInstance

end Section_1_5


section Section_1_6

/-- The category of right-exact endofunctors of an additive category inherits a monoidal
structure from composition: the unit (the identity functor) is right-exact and composition
of right-exact functors is right-exact. -/
noncomputable instance rightExactEndofunctor_isMonoidal
    (C : Type*) [Category C] :
    (rightExactFunctor C C).IsMonoidal where
  prop_unit := by
    simp only [rightExactFunctor_iff]
    exact Limits.PreservesColimitsOfSize0.preservesFiniteColimits (𝟭 C)
  prop_tensor := by
    intro F G hF hG
    simp only [rightExactFunctor_iff] at hF hG ⊢
    exact Limits.comp_preservesFiniteColimits F G

end Section_1_6
end Section_1_2
end TensorCategories
