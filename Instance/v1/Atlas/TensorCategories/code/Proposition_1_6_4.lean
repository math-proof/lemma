/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_6_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.End
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section

set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory


attribute [local instance] endofunctorMonoidalCategory

universe u v


namespace Prop164

/-- The full subcategory of right-exact endofunctors of `C` is monoidal: the identity
functor is right-exact, and a composition of right-exact functors is right-exact. -/
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

end Prop164
