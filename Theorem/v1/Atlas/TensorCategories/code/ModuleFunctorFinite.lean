/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Class.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
public import Theorem.Category.Atlas.v1.TensorCategories.code.ModuleFunctorDefs
public import Theorem.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
public import Abbrev.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
public import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
set_option maxHeartbeats 800000

open CategoryTheory

public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

/-- The category of module functors between two left `C`-module categories carries a
canonical abelian structure. -/


