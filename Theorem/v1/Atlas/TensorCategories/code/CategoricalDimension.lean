/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CategoricalDimension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory MonoidalCategory Category Limits

public section

universe v u


namespace TensorCategories

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
  [PivotalCategory C]

end TensorCategories
