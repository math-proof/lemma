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
public import Abbrev.v1.Atlas.TensorCategories.code.BasicMonoidalDefs.Part4

@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category


attribute [instance] endofunctorMonoidalCategory

universe v₁ v₂ u₁ u₂


namespace TensorCategories

section Section_1_2

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

section Section_1_7

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

variable {A : Type*} [CommGroup A]

/-- The cocycle condition describing the data of a monoidal functor between two
3-cocycle-twisted vector-space categories `Vec_{G₁}^{ω₁} → Vec_{G₂}^{ω₂}` associated to a
group homomorphism `f` and a 2-cochain `μ`. -/
def IsMonoidalFunctorDatum
    (ω₁ : G₁ → G₁ → G₁ → A) (ω₂ : G₂ → G₂ → G₂ → A)
    (f : G₁ →* G₂) (μ : G₁ → G₁ → A) : Prop :=
  ∀ g h l : G₁,
    ω₁ g h l * μ (g * h) l * μ g h =
    μ g (h * l) * μ h l * ω₂ (f g) (f h) (f l)

/-- The cohomological condition characterising when a 1-cochain `η : G₁ → A` provides a
monoidal natural transformation between two monoidal functors with cochain data `μ` and
`μ'`. -/
def IsMonoidalTransformationDatum
    (μ μ' : G₁ → G₁ → A) (η : G₁ → A) : Prop :=
  ∀ g h : G₁, μ' g h * η g * η h = η (g * h) * μ g h

end Section_1_7
end Section_1_2
end TensorCategories
