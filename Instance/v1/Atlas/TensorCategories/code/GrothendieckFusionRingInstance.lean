/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckFusionRingInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Class.v1.Atlas.TensorCategories.code.GrothendieckFusionRingInstance
open CategoryTheory MonoidalCategory Finset

universe v u


namespace CategoryTheory

/-- Any `CategoricalFusionData` directly supplies Jordan-Hölder multiplicities by reading off
its built-in multiplicity function and the associated axioms. -/
instance hasJordanHolderMultiplicities_of_categoricalFusionData
    (κ : Type*) [Field κ] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear κ C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
    [RigidCategory C]
    [cfd : CategoricalFusionData κ C] :
    HasJordanHolderMultiplicities κ C where
  mult := cfd.mult
  mult_simple := cfd.mult_simple
  mult_unit := cfd.mult_unit
  mult_tensor := cfd.mult_tensor
  mult_iso := cfd.mult_iso
  mult_nontrivial := cfd.mult_nontrivial

end CategoryTheory
