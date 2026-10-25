/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellCount.Part2
import Theorem.StatisticalMechanics.Code.Onsager.CellEuler.Part2


namespace StatMech.Onsager.CellEuler

open Finset StatMech.Onsager.CellCount


def edgesOf (c : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {(2 * c.1 + 1, 2 * c.2), (2 * c.1 + 1, 2 * c.2 + 2),
    (2 * c.1, 2 * c.2 + 1), (2 * c.1 + 2, 2 * c.2 + 1)}


def cellEdges (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) := S.biUnion edgesOf


def eulerChar (S : Finset (ℤ × ℤ)) : ℤ :=
  ((cellVerts S).card : ℤ) - (cellEdges S).card + S.card


end StatMech.Onsager.CellEuler
