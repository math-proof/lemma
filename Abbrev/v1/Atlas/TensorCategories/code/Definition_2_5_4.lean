/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_2_5_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Category.Basic
public import Class.v1.Atlas.TensorCategories.code.Definition_2_5_4
@[expose] public section

open CategoryTheory MonoidalCategory

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

/-- Alias for `Definition_2_5_4_BimoduleCategory`: a `(C, D)`-bimodule category. -/
abbrev Definition_2_5_4 := @Definition_2_5_4_BimoduleCategory

end CategoryTheory
