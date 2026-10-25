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


namespace GeometricAlgebra

/-- Abbreviation for the general linear group `GL(V)` of a `k`-module `V`. -/
abbrev GLV (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] :=
  LinearMap.GeneralLinearGroup k V

end GeometricAlgebra
