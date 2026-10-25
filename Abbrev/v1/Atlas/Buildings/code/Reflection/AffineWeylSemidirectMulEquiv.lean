/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylSemidirectMulEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylGroupConstruction
import Mathlib.GroupTheory.SemidirectProduct
import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylSemidirectMulEquiv
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineWeylGroupData

variable (d : AffineWeylGroupData E)

/-- The abstract semidirect product $Λ(\check Φ) ⋊ W$ associated to the affine Weyl
group data. -/
abbrev AffineWeylSemidirect :=
  (Multiplicative ↥d.corootLattice) ⋊[d.weylActionMulAutHom] ↥d.weylGroup

end AffineWeylGroupData
end
