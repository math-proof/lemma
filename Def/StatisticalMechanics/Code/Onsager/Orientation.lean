/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Orientation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WalkCellBridge


namespace StatMech.Onsager.Orientation

open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity

open Fin.NatCast

variable {n : ℕ} [NeZero n]


def leftCell : Fin 4 → ℤ × ℤ → ℤ × ℤ
  | 0, p => p
  | 1, p => (p.1 - 1, p.2)
  | 2, p => (p.1 - 1, p.2 - 1)
  | 3, p => (p.1, p.2 - 1)


end StatMech.Onsager.Orientation
