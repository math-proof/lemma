/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecInstances.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
public import Abbrev.v1.Atlas.TensorCategories.code.VecInstances

@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits

universe v u


noncomputable section

namespace VecInstances

/-- `Vec k` has all finite biproducts, obtained from existence of finite products. -/
instance hasFiniteBiproducts_vec (k : Type u) [Field k] :
    HasFiniteBiproducts (Vec k) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end VecInstances
end
