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
import Instance.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical
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

/-- The basis class in the Grothendieck ring corresponding to the simple object `S i`. -/
def basisClass (i : cfd.ι) : GrothendieckRingK0 (κ := κ) (C := C) :=
  ⟨FusionRing.basisVec i⟩

/-- Fusion coefficients for `Rep(ℤ/2)`: a one-dimensional Hom space iff `i + j ≡ k (mod 2)`. -/
def N_categorical (i j k : Fin 2) : ℕ :=
  if (i.val + j.val) % 2 = k.val then 1 else 0

end RepZ2Categorical

namespace FusionCategoryBridge

open CategoricalFusionData FusionRing

variable {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear κ C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
  [RigidCategory C]

variable [cfd : CategoricalFusionData κ C]

/-- Alternative name for the basis class of the simple `S i` in the Grothendieck ring,
used by the fusion-category bridge. -/
def simpleClass (i : cfd.ι) : GrRingOf (toFusionRing (κ := κ) (C := C)) :=
  ⟨basisVec i⟩

end FusionCategoryBridge
