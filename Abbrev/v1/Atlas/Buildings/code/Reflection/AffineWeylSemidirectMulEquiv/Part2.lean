/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylSemidirectMulEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylGroupConstruction
public import Mathlib.GroupTheory.SemidirectProduct
public import Structure.v1.Atlas.Buildings.code.Reflection.AffineWeylSemidirectMulEquiv
open scoped InnerProductSpace
open Set


@[expose] public noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineWeylSemidirectData

variable (d : AffineWeylSemidirectData E)

/-- Shorthand for the abstract semidirect product type. -/
abbrev SemiType := d.toAffineWeylGroupData.AffineWeylSemidirect

end AffineWeylSemidirectData
end
