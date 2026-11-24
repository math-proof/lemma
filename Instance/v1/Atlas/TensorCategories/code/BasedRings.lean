module
public import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
public import Theorem.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
public import Theorem.Category.Atlas.v1.TensorCategories.code.GradedVec
public import Theorem.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
public import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
public import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
public import Theorem.v1.Atlas.TensorCategories.code.BasedRings
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- The setoid on normalized 3-cocycles induced by cohomology equivalence. -/
instance cocycleCohomologousSetoid (G : Type*) [Group G] (A : Type*) [CommGroup A] :
    Setoid (NormalizedGroupCocycle3 G A) where
  r := CocycleCohomologous
  iseqv := ⟨cocycleCohomologous_refl,
            fun h => cocycleCohomologous_symm h,
            fun h₁ h₂ => cocycleCohomologous_trans h₁ h₂⟩

end FusionRing
