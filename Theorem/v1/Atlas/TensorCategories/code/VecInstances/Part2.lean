/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecInstances.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
import Def.v1.Atlas.TensorCategories.code.VecInstances
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits

universe v u


noncomputable section

namespace VecInstances

section FiniteLength

variable (k : Type u) [Field k]

/-- Every object of `Vec k` has finite length: its subobject lattice is both
well-founded and inverse well-founded. -/
theorem hasFiniteLength_vec (X : Vec k) :
    TensorCategories.HasFiniteLength X :=
  let emb := subobjectOrderEmbedding k X
  ⟨emb.wellFoundedLT, emb.wellFoundedGT⟩

end FiniteLength
end VecInstances
end
