/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRingCategorical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.Prop_1_45_10
import Structure.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part2
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

/-- Categorical multitensor data for a `κ`-linear monoidal preadditive category `C`: a finite
set of representatives `S i` of simples together with fusion coefficients `N`, a unit set `I₀`,
involution and the based-ring axioms. Used to model multitensor (not necessarily tensor)
categories. -/
class CategoricalMultitensorData (κ : Type*) [Field κ] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear κ C]
    [MonoidalCategory C] [MonoidalPreadditive C] where
  ι : Type
  [ι_fintype : Fintype ι]
  [ι_deceq : DecidableEq ι]
  S : ι → C
  S_simple : ∀ i, Simple (S i)
  N : ι → ι → ι → ℕ
  N_eq_finrank : ∀ i j k, N i j k = Module.finrank κ (S k ⟶ (S i ⊗ S j))
  I₀ : Finset ι
  star : ι → ι
  star_star : ∀ i, star (star i) = i
  N_assoc : ∀ i j m l, ∑ p : ι, N i j p * N p m l = ∑ p : ι, N j m p * N i p l
  N_sum_I₀_mul_left : ∀ j k, (∑ p ∈ I₀, N p j k) = if j = k then 1 else 0
  N_sum_I₀_mul_right : ∀ i k, (∑ p ∈ I₀, N i p k) = if i = k then 1 else 0
  N_duality_trace : ∀ i j, (∑ k ∈ I₀, N i j k) = if i = star j then 1 else 0
  N_star_anti : ∀ i j k, N i j k = N (star j) (star i) (star k)

end FusionCategoryBridge
