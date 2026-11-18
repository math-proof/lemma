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
public import Instance.v1.Atlas.TensorCategories.code.VecInstances.Part2

@[expose] public section
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits

universe v u


noncomputable section

namespace VecInstances

section FiniteLength

variable (k : Type u) [Field k]

/-- Two `k`-linear endomorphisms of `k` are equal iff they agree on the multiplicative
identity. -/
public theorem linearMap_eq_of_apply_one (f g : k →ₗ[k] k) (h : f 1 = g 1) : f = g := by
  ext; exact h

end FiniteLength
end VecInstances
end
