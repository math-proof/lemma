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
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz


namespace StatMech.Universality

open Finset

open StatMech.Onsager.BaseCase

open StatMech.Onsager


structure HexAWBrickCycle (n : ℕ) [NeZero n] where
  coord : Fin n → HexAWCoord
  edge : Fin n → Fin 3
  adjacent : ∀ i, hexAWNeighbor (coord i) (edge i) = coord (i + 1)
  coord_injective : Function.Injective coord

end StatMech.Universality
