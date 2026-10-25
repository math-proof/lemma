/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCellBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WalkCellLocal
import Theorem.StatisticalMechanics.Code.Onsager.WalkCellBridge


namespace StatMech.Onsager.WalkCellBoundary

open Finset SimpleGraph Set

open StatMech.Lattice

open StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.WalkCrossing StatMech.Onsager.JordanParity
  StatMech.Onsager.JedBridge StatMech.Onsager.WalkCellRegion
  StatMech.Onsager.WalkCellLocal StatMech.Onsager.CellCount
  StatMech.Onsager.CellEuler StatMech.Onsager.CellPinch
  StatMech.Onsager.CellConnect StatMech.Onsager.WalkCellBridge

variable {m : ℕ}


def leftCell (d : Fin (m + 3) → Fin 4) (k : Fin (m + 3)) : ℤ × ℤ :=
  match d k with
  | 0 => ((pos d k).1, (pos d k).2)
  | 1 => ((pos d k).1 - 1, (pos d k).2)
  | 2 => ((pos d k).1 - 1, (pos d k).2 - 1)
  | 3 => ((pos d k).1, (pos d k).2 - 1)


def rightCell (d : Fin (m + 3) → Fin 4) (k : Fin (m + 3)) : ℤ × ℤ :=
  match d k with
  | 0 => ((pos d k).1, (pos d k).2 - 1)
  | 1 => ((pos d k).1, (pos d k).2)
  | 2 => ((pos d k).1 - 1, (pos d k).2)
  | 3 => ((pos d k).1 - 1, (pos d k).2 - 1)

end StatMech.Onsager.WalkCellBoundary
