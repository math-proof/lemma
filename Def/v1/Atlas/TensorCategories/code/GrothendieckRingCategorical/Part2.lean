/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRingCategorical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical
public import Def.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
public import Structure.v1.Atlas.TensorCategories.code.GrothendieckRing
public import Structure.v1.Atlas.TensorCategories.code.FrobeniusPerron
public import Class.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical

@[expose] public section
open CategoryTheory MonoidalCategory Limits Finset
open TensorCategories

universe v u


namespace CategoricalFusionData

variable {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear κ C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
  [RigidCategory C]

variable [cfd : CategoricalFusionData κ C]

/-- The basis class in the Grothendieck ring corresponding to the simple object S i. -/
def basisClass (i : cfd.ι) : FusionRing.GrRingOf (toFusionRing (κ := κ) (C := C)) :=
  ⟨FusionRing.basisVec i⟩

end CategoricalFusionData

namespace RepZ2Categorical

/-- Fusion coefficients for Rep(ℤ/2): a one-dimensional Hom space iff i + j ≡ k (mod 2). -/
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

/-- Alternative name for the basis class of the simple S i in the Grothendieck ring,
used by the fusion-category bridge. -/
def simpleClass (i : cfd.ι) : GrRingOf (toFusionRing (κ := κ) (C := C)) :=
  ⟨basisVec i⟩

end FusionCategoryBridge
