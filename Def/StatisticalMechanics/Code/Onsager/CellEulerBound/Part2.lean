/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEuler.Part3
import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part4
import Theorem.StatisticalMechanics.Code.Onsager.CellEulerBound


namespace StatMech.Onsager.CellEulerBound

open Finset SimpleGraph

open StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


def topEdge (c : Cell) : Sym2 Vtx :=
  s((c.1, c.2 + 1), (c.1 + 1, c.2 + 1))


def topEdges (S : Finset Cell) : Finset (Sym2 Vtx) := S.image topEdge

end StatMech.Onsager.CellEulerBound
