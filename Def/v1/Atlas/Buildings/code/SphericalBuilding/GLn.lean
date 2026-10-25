/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.RelClasses
import Mathlib.Data.Matrix.Basic
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.GLn


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- A `SubspaceFlag` is a chamber iff its chain has length $n-1$, i.e.\ it is a maximal flag. -/
def IsChamber (F : SubspaceFlag k n) : Prop :=
  F.chain.length = n - 1

end GLnBuilding
