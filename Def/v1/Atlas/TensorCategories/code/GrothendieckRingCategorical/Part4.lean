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
import Class.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part2
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

namespace CategoricalMultitensorData

variable {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear κ C]
  [MonoidalCategory C] [MonoidalPreadditive C]

variable [cmd : CategoricalMultitensorData κ C]


attribute [reducible, instance] CategoricalMultitensorData.ι_fintype
  CategoricalMultitensorData.ι_deceq

/-- Extract a `BasedRing` from `CategoricalMultitensorData`, realising the Grothendieck
based ring of a multitensor category. -/
def toBasedRing : BasedRing cmd.ι where
  N := cmd.N
  I₀ := cmd.I₀
  star := cmd.star
  star_star := cmd.star_star
  assoc := cmd.N_assoc
  sum_I₀_mul_left := cmd.N_sum_I₀_mul_left
  sum_I₀_mul_right := cmd.N_sum_I₀_mul_right
  duality_trace := cmd.N_duality_trace
  star_anti := cmd.N_star_anti

end CategoricalMultitensorData
end FusionCategoryBridge
