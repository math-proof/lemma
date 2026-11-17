/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ZPlusModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Structure.v1.Atlas.TensorCategories.code.ZPlusModules.Part4

@[expose] public section

set_option maxHeartbeats 800000

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {R : ZPlusRing ι} {κ : Type*} [DecidableEq κ] [Fintype κ]


namespace ZPlusModule

variable (M : ZPlusModule R κ)

/-- A `ℤ_+`-module is irreducible if it has no proper nonempty `ℤ_+`-submodule. -/
def IsIrreducible : Prop := ∀ S : Finset κ, ¬M.IsZPlusSubmodule S

end ZPlusModule
