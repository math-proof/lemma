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

@[expose] public section


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- The ambient vector space $k^n$ realised as the function type $\mathrm{Fin}\ n \to k$. -/
abbrev Vec := Fin n → k

end GLnBuilding
