/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecSemisimple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
import Lemma.Category.Atlas.v1.TensorCategories.code.VecInstances
import Abbrev.v1.Atlas.TensorCategories.code.VecInstances.Part2
import Def.v1.Atlas.TensorCategories.code.VecSemisimple
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits Module

universe u


noncomputable section

namespace VecSemisimple

variable (k : Type u) [Field k]

/-- `FGModuleCat k` is a semisimple category: every finite-dimensional `k`-vector
space splits as a direct sum of `dim_k(X)` copies of the simple object `k`. -/
instance hasFinitelyManySimples_vec :
    TensorCategories.HasFinitelyManySimples (FGModuleCat.{u} k) where
  finiteSimples := ⟨1, fun _ => FGModuleCat.of k k, ⟨fun _ => simple_of_k k,
    fun X _hX => ⟨0, ⟨simple_iso_of_k k X⟩⟩⟩⟩

end VecSemisimple
end
