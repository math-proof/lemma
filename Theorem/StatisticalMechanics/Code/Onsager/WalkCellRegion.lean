/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEulerBound.Part4
import Theorem.StatisticalMechanics.Code.Onsager.InsideConnected
import Def.StatisticalMechanics.Code.Onsager.JedBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part8
import Def.StatisticalMechanics.Code.Onsager.WalkCellRegion


namespace StatMech.Onsager.WalkCellRegion

open Finset SimpleGraph Set

open StatMech.Lattice

open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.JordanParity
  StatMech.Onsager.InsideConnected StatMech.Onsager.JedBridge


@[simp] theorem cellFace_zero (p : ℤ × ℤ) : cellFace p 0 = p.1 := rfl

@[simp] theorem cellFace_one (p : ℤ × ℤ) : cellFace p 1 = p.2 := rfl

@[simp] theorem cellFace_symm (z : Site 2) : cellFace.symm z = (z 0, z 1) := rfl

end StatMech.Onsager.WalkCellRegion
