/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRingCategorical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
public import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
public import Lemma.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
public import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
public import Lemma.Category.Atlas.v1.TensorCategories.code.Prop_1_45_10
public import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part2
public section

open CategoryTheory MonoidalCategory Limits Finset
open TensorCategories

universe v u


namespace FusionCategoryBridge

open CategoricalFusionData FusionRing

variable {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear κ C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
  [RigidCategory C]

variable [cfd : CategoricalFusionData κ C]

/-- Definition 1.42.2(1): A based ring on the basis `ι`: fusion coefficients, a unit subset
`I₀`, an involution `star`, associativity, and the duality / antiautomorphism axioms. -/
structure BasedRing (ι : Type*) [DecidableEq ι] [Fintype ι] where
  N : ι → ι → ι → ℕ
  I₀ : Finset ι
  star : ι → ι
  star_star : ∀ i, star (star i) = i
  assoc : ∀ i j k l, ∑ m : ι, N i j m * N m k l = ∑ m : ι, N j k m * N i m l
  sum_I₀_mul_left : ∀ j k, (∑ s ∈ I₀, N s j k) = if j = k then 1 else 0
  sum_I₀_mul_right : ∀ i k, (∑ s ∈ I₀, N i s k) = if i = k then 1 else 0
  duality_trace : ∀ i j, (∑ k ∈ I₀, N i j k) = if i = star j then 1 else 0
  star_anti : ∀ i j k, N i j k = N (star j) (star i) (star k)

end FusionCategoryBridge
