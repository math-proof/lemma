/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellLocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WalkCellRegion.Part7
import Theorem.StatisticalMechanics.Code.Onsager.CellGaussBonnetGlobal


namespace StatMech.Onsager.WalkCellLocal

open Finset SimpleGraph Set

open StatMech.Lattice

open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.JordanParity
  StatMech.Onsager.JedBridge StatMech.Onsager.WalkCellRegion
  StatMech.Onsager.CellCount StatMech.Onsager.CellEuler StatMech.Onsager.CellPinch

section Walk

variable {m : ℕ}

variable (d : Fin (m + 3) → Fin 4)
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d))
  (hreflexfree : ∀ i : Fin (m + 3), d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)

local notation "S" => interiorCells d hclosed hsimple hreflexfree

local notation "P" => walkP d hclosed hsimple

local notation "R" => walkRegionGraph d hclosed hsimple


end Walk
end StatMech.Onsager.WalkCellLocal
