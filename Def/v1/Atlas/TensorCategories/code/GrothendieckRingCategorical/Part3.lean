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
import Structure.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical
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

/-- A based ring is unital (Definition 1.42.2(2)) if `1` itself belongs to the basis,
i.e. `I₀` is a singleton. -/
def BasedRing.IsUnital {ι : Type*} [DecidableEq ι] [Fintype ι]
    (B : BasedRing ι) : Prop :=
  ∃ u : ι, B.I₀ = {u}

end FusionCategoryBridge
