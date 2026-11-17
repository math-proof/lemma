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
public import Structure.v1.Atlas.TensorCategories.code.BasicMonoidalDefs.Part3

@[expose] public section

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
