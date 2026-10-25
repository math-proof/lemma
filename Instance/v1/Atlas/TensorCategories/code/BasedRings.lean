/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Lemma.Category.Atlas.v1.TensorCategories.code.GradedVec
import Lemma.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
import Theorem.v1.Atlas.TensorCategories.code.BasedRings
open Finset


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
