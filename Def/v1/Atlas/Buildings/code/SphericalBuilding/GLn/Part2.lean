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
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.GLn.Part2


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- A subspace $W$ is compatible with the frame $F$ iff $W = \bigoplus_{i \in S} L_i$ for some
$S \subseteq \{1,\dots,n\}$. -/
def Frame.IsCompatible (F : Frame k n) (W : Submodule k (Vec k n)) : Prop :=
  ∃ S : Finset (Fin n), W = ⨆ i ∈ S, F.lines i

end GLnBuilding
