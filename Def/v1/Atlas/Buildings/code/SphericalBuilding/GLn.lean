/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Order.RelClasses
public import Mathlib.Data.Matrix.Basic
public import Structure.v1.Atlas.Buildings.code.SphericalBuilding.GLn

@[expose] public section

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- A `SubspaceFlag` is a chamber iff its chain has length $n-1$, i.e.\ it is a maximal flag. -/
def IsChamber (F : SubspaceFlag k n) : Prop :=
  F.chain.length = n - 1

end GLnBuilding
