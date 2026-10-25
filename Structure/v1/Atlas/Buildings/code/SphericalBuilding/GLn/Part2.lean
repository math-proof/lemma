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
import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLn


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- A frame of $k^n$: an ordered direct-sum decomposition $k^n = L_1 \oplus \cdots \oplus L_n$
into $n$ lines. -/
structure Frame where
  lines : Fin n → Submodule k (Vec k n)
  one_dim : ∀ i, Module.finrank k (lines i) = 1
  indep : iSupIndep lines
  spanning : ⨆ i, lines i = ⊤

end GLnBuilding
