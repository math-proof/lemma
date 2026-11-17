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
public import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part3
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

/-- A `UnitalBasedRing` is a based ring together with a distinguished basis element `unitElem`
which is the unique element of `I₀`. -/
structure UnitalBasedRing (ι : Type*) [DecidableEq ι] [Fintype ι]
    extends BasedRing ι where
  unitElem : ι
  I₀_eq_singleton : I₀ = {unitElem}

end FusionCategoryBridge
