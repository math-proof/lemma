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
import Instance.v1.Atlas.TensorCategories.code.GrothendieckFusionRingInstance
open CategoryTheory MonoidalCategory Finset

universe v u


namespace CategoryTheory

section JHLift

variable {κ : Type*} [Field κ] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear κ C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear κ C]
  [RigidCategory C]
  [cfd : CategoricalFusionData κ C]
  [jh : HasJordanHolderMultiplicities κ C]

/-- Lifts a Frobenius-Perron dimension defined on simples to all objects of `C` by
summing multiplicities weighted by `fpd.d`. -/
noncomputable def jhFpDim
    (fpd : (CategoricalFusionData.toFusionRing (κ := κ) (C := C)).FPdimData)
    (X : C) : ℝ :=
  ∑ i : cfd.ι, (jh.mult X i : ℝ) * fpd.d i

end JHLift
end CategoryTheory
