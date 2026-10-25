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
import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical
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

/-- Abbreviation for the underlying additive group `K₀` of the Grothendieck ring obtained
from the categorical fusion data on `C`. -/
abbrev GrothendieckRingK0 : Type :=
  FusionRing.GrRingOf (toFusionRing (κ := κ) (C := C))

end CategoricalFusionData
