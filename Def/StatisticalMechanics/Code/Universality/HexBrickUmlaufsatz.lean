/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBrickUmlaufsatz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18


namespace StatMech.Universality

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager


def hexBrickDir : Fin 6 → Fin 4 := ![2, 2, 1, 0, 0, 3]


def hexBrickPos (c : HexAWCoord) : ℤ × ℤ :=
  match c.color with
  | .black => (2 * c.i + c.j, -c.j)
  | .white => (2 * c.i + c.j + 1, -c.j)


def hexAWHeadingMod (c : HexAWCoord) (e : Fin 3) : Fin 6 :=
  match c.color, e with
  | .black, 0 => 4
  | .black, 1 => 0
  | .black, 2 => 2
  | .white, 0 => 1
  | .white, 1 => 3
  | .white, 2 => 5


end StatMech.Universality
