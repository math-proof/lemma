/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ConcreteModuleCategories.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Class.v1.Atlas.TensorCategories.code.ConcreteModuleCategories.Part2
@[expose] public section
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ vₘ w u₁ u₂ u₃ uₘ


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

section BimoduleCategory

/-- Shorthand for `Definition_2_5_4_BimoduleCategory`. -/
abbrev Definition_2_5_4 :=
  @Definition_2_5_4_BimoduleCategory

end BimoduleCategory
end CategoryTheory
