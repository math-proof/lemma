/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftWilsonComponentGrouplike.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part8
public import Theorem.Category.Atlas.v1.TensorCategories.code.CoradicalFiltration
open scoped TensorProduct
open Coalgebra

public section

universe u v

variable {R : Type u} {C : Type v}
variable [Field R] [AddCommGroup C] [Module R C] [Coalgebra R C]


