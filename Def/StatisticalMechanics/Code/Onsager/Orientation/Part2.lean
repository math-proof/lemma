/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Orientation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WalkCellBridge
import Theorem.StatisticalMechanics.Code.Onsager.Orientation


namespace StatMech.Onsager.Orientation

open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind StatMech.Onsager.WalkCrossing
  StatMech.Onsager.JordanParity

open Fin.NatCast

variable {n : ℕ} [NeZero n]


def leftParity (d : Fin n → Fin 4) (k : Fin n) : ZMod 2 :=
  rayParity d (leftCell (d k) (pos d k)).1 (leftCell (d k) (pos d k)).2


end StatMech.Onsager.Orientation
