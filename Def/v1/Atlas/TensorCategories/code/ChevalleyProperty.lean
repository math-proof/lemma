/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ChevalleyProperty.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.SemisimpleMultitensor
import Class.v1.Atlas.TensorCategories.code.ChevalleyProperty
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v u


noncomputable section

namespace CategoryTheory

section ChevalleyProperty

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- Definition 1.31.1 (named restatement): the Chevalley property for a tensor category. -/
def Definition_1_31_1_ChevalleyProperty : Prop :=
  HasChevalleyProperty C

/-- Definition 1.31.1: the Chevalley property for a tensor category, expressed as a
proposition. -/
def Definition_1_31_1 : Prop :=
  HasChevalleyProperty C

end ChevalleyProperty
end CategoryTheory
end
