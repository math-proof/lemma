/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyProperty.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.SemisimpleMultitensor
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section ChevalleyProperty

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- A monoidal category `C` has the Chevalley property if the tensor product of two
semisimple objects is again semisimple (so the full subcategory of semisimple objects is a
monoidal subcategory). -/
class HasChevalleyProperty : Prop where
  tensor_semisimple : ∀ (X Y : C),
    IsSemisimpleObject C X → IsSemisimpleObject C Y → IsSemisimpleObject C (X ⊗ Y)

end ChevalleyProperty
end CategoryTheory
end
