/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylSemidirectMulEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylGroupConstruction
import Mathlib.GroupTheory.SemidirectProduct
import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylSemidirectMulEquiv.Part2
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineWeylSemidirectData

variable (d : AffineWeylSemidirectData E)

theorem toSemidirect_surjective : Function.Surjective d.toSemidirect := by
  sorry

theorem toSemidirect_injective : Function.Injective d.toSemidirect := by
  sorry

theorem toSemidirect_mul (x y : d.affineWeylSubgroup) :
    d.toSemidirect (x * y) = d.toSemidirect x * d.toSemidirect y := by
  sorry

end AffineWeylSemidirectData
end
