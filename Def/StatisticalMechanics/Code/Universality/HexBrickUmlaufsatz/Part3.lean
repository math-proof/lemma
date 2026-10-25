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
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part2


namespace StatMech.Universality

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager


namespace HexAWBrickCycle

noncomputable def ofList (coords : List HexAWCoord)
    [NeZero coords.length] (hnodup : coords.Nodup)
    (hadjacent : ∀ i : Fin coords.length, ∃ e : Fin 3,
      hexAWNeighbor (coords.get i) e = coords.get (i + 1)) :
    HexAWBrickCycle coords.length where
  coord := coords.get
  edge i := (hadjacent i).choose
  adjacent i := (hadjacent i).choose_spec
  coord_injective := hnodup.injective_get

end HexAWBrickCycle


def hexBrickTurnPotential : Fin 6 → ℤ := ![0, 2, 1, 0, 2, 1]


def hexHeadingTurn (h : Fin 6) (t : ℤ) : Fin 6 :=
  if t = 1 then h + 1 else h - 1


end StatMech.Universality
