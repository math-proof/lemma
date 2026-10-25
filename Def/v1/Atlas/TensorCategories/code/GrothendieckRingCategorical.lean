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
import Class.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical
open CategoryTheory MonoidalCategory Limits Finset
open TensorCategories

universe v u


namespace CategoricalFusionData

variable {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear κ C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
  [RigidCategory C]

variable [cfd : CategoricalFusionData κ C]


attribute [reducible, instance] CategoricalFusionData.ι_fintype CategoricalFusionData.ι_deceq

/-- The combinatorial `FusionRing` (Definition 1.42.2 / Proposition 1.42.4) extracted from
the categorical fusion data on `C`. -/
def toFusionRing : FusionRing cfd.ι where
  unit := cfd.unitIdx
  N := cfd.N
  star := cfd.star
  star_star := cfd.star_star
  unit_mul := cfd.N_unit_mul
  mul_unit := cfd.N_mul_unit
  duality := cfd.N_duality
  assoc := cfd.N_assoc
  N_star_transpose := cfd.N_star_transpose

end CategoricalFusionData
