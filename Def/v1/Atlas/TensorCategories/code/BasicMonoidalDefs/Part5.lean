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
import Abbrev.v1.Atlas.TensorCategories.code.BasicMonoidalDefs.Part4
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
