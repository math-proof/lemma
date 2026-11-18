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
@[expose] public noncomputable section
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits

universe v u



namespace VecInstances

/-- `Vec k` is the category of finite-dimensional `k`-vector spaces, modeled in
mathlib by `FGModuleCat k`. -/
abbrev Vec (k : Type u) [Ring k] := FGModuleCat.{u} k

end VecInstances
end
