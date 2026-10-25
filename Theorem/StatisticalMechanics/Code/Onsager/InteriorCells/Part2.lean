/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorCells.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.JordanParity
import Theorem.StatisticalMechanics.Code.Onsager.WalkCrossingV.Part2
import Def.StatisticalMechanics.Code.Onsager.InteriorCells.Part2


namespace StatMech.Onsager.InteriorCells

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.WalkCrossingV StatMech.Onsager.JordanParity

variable {n : ℕ} [NeZero n]


theorem mem_interiorCells (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (c : ℤ × ℤ) :
    c ∈ interiorCells d hclosed ↔ rayParity d c.1 c.2 = 1 := by
  unfold interiorCells
  rw [Set.Finite.mem_toFinset]
  rfl

end StatMech.Onsager.InteriorCells
