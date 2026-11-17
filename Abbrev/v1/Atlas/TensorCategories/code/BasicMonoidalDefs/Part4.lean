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
public import Instance.v1.Atlas.TensorCategories.code.BasicMonoidalDefs
@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category


attribute [instance] endofunctorMonoidalCategory

universe v₁ v₂ u₁ u₂


namespace TensorCategories

section Section_1_2

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

section Section_1_6

/-- The enveloping algebra `A^e := A ⊗_k A^{op}` of a `k`-algebra `A`. -/
abbrev EnvelopingAlgebra (k : Type*) [CommRing k] (A : Type*) [Ring A] [Algebra k A] :=
  TensorProduct k A (MulOpposite A)

/-- Eilenberg–Watts equivalence: for a finite-dimensional `k`-algebra `A`, the category of
`A^e`-modules is equivalent to the category of right-exact endofunctors of `Mod A`. -/

end Section_1_6


section Section_1_7

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

variable {A : Type*} [CommGroup A]

/-- Definition 1.4.5 (alias): packages a `Functor.Monoidal` instance for a functor
between monoidal categories. -/
abbrev Definition_1_4_5_MonoidalFunctor
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (F : C ⥤ D) [hF : F.Monoidal] : Functor.Monoidal F :=
  hF

end Section_1_7
end Section_1_2
end TensorCategories
