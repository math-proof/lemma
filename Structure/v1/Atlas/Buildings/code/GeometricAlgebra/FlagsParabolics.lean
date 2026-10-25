/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Group
import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics.Part2


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- A flag in a `k`-vector space `V` is a strictly increasing sequence of submodules
`spaces : Fin len → Submodule k V`. -/
structure Flag (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] where
  len : ℕ
  spaces : Fin len → Submodule k V
  strictMono : StrictMono spaces

end GeometricAlgebra
