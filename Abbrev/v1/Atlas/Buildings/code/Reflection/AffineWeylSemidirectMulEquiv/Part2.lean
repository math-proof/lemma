/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylSemidirectMulEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylGroupConstruction
import Mathlib.GroupTheory.SemidirectProduct
import Structure.v1.Atlas.Buildings.code.Reflection.AffineWeylSemidirectMulEquiv
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineWeylSemidirectData

variable (d : AffineWeylSemidirectData E)

/-- Shorthand for the abstract semidirect product type. -/
abbrev SemiType := d.toAffineWeylGroupData.AffineWeylSemidirect

end AffineWeylSemidirectData
end
