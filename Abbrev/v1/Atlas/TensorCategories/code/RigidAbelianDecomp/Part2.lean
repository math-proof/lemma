module
public import Theorem.v1.Atlas.TensorCategories.code.MacLaneCoherence
public import Theorem.Category.Atlas.v1.TensorCategories.code.MacLaneCoherence
public import Theorem.Category.Atlas.v1.TensorCategories.code.MacLaneStrictness
public import Theorem.Category.Atlas.v1.TensorCategories.code.InvertibleObjects
public import Theorem.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
public import Theorem.Category.Atlas.v1.TensorCategories.code.TensorExact
public import Theorem.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
public import Instance.v1.Atlas.TensorCategories.code.MacLaneStrictness.Part2
public import Instance.v1.Atlas.TensorCategories.code.InvertibleObjects
public import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
public import Def.v1.Atlas.TensorCategories.code.TensorExact.Part3
public import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
public import Abbrev.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
public import Def.v1.Atlas.TensorCategories.code.RigidAbelianDecomp
set_option maxHeartbeats 800000
open CategoryTheory MonoidalCategory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RigidAbelianDecomp.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-- Reference abbreviation for the definition of a finite abelian category. -/
abbrev IsFiniteAbelianCategory_def := @IsFiniteAbelianCategory

