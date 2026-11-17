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
public import Structure.v1.Atlas.Buildings.code.SphericalBuilding.GLn.Part2

@[expose] public section

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- A subspace $W$ is compatible with the frame $F$ iff $W = \bigoplus_{i \in S} L_i$ for some
$S \subseteq \{1,\dots,n\}$. -/
def Frame.IsCompatible (F : Frame k n) (W : Submodule k (Vec k n)) : Prop :=
  ∃ S : Finset (Fin n), W = ⨆ i ∈ S, F.lines i

end GLnBuilding
