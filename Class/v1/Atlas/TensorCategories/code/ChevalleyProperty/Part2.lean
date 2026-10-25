/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyProperty.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.SemisimpleMultitensor
import Def.v1.Atlas.TensorCategories.code.ChevalleyProperty
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section Pointed

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- A monoidal category is pointed in this Atlas formulation if every simple object has a
tensor inverse, i.e. is invertible. -/
class IsPointedTensorCategory : Prop where
  simple_has_inverse : ∀ (X : C) [Simple X],
    ∃ (Y : C), Nonempty (X ⊗ Y ≅ 𝟙_ C) ∧ Nonempty (Y ⊗ X ≅ 𝟙_ C)

end Pointed
end CategoryTheory
end
