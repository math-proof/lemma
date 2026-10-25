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


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- The ambient vector space $k^n$ realised as the function type $\mathrm{Fin}\ n \to k$. -/
abbrev Vec := Fin n → k

end GLnBuilding
