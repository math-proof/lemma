/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/BasisExtensionChain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnCommonApartment
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Structure.v1.Atlas.Buildings.code.SphericalBuilding.BasisExtensionChain

@[expose] public section

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Wrap `AdaptedBasisHyp` as a `SimultaneousRefinementHyp` — they are the same property
phrased identically. -/
noncomputable def simultaneousRefinementOfAdapted
    (h : AdaptedBasisHyp k n) : SimultaneousRefinementHyp k n where
  refine_list := h.adapt

end GLnBuilding
