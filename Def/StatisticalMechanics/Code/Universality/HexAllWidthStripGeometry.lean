/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexAllWidthStripGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
import Structure.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

noncomputable def hexAWAxis : ℂ := hexUnit 4


noncomputable def hexAWBasisI : ℂ := hexUnit 4 - hexUnit 0


noncomputable def hexAWBasisJ : ℂ := hexUnit 4 - hexUnit 2


noncomputable def hexAWPos (c : HexAWCoord) : ℂ :=
  (c.i : ℂ) * hexAWBasisI + (c.j : ℂ) * hexAWBasisJ +
    match c.color with
    | .black => 0
    | .white => hexAWAxis


def hexAWHeading (c : HexAWCoord) (e : Fin 3) : ℤ :=
  match c.color, e with
  | .black, 0 => 4
  | .black, 1 => 0
  | .black, 2 => 2
  | .white, 0 => 7
  | .white, 1 => 3
  | .white, 2 => 5


def hexAWNeighbor (c : HexAWCoord) (e : Fin 3) : HexAWCoord :=
  match c.color, e with
  | .black, 0 => ⟨c.i, c.j, .white⟩
  | .black, 1 => ⟨c.i - 1, c.j, .white⟩
  | .black, 2 => ⟨c.i, c.j - 1, .white⟩
  | .white, 0 => ⟨c.i, c.j, .black⟩
  | .white, 1 => ⟨c.i + 1, c.j, .black⟩
  | .white, 2 => ⟨c.i, c.j + 1, .black⟩


noncomputable def hexAWMid (c : HexAWCoord) (e : Fin 3) : ℂ :=
  (hexAWPos c + hexAWPos (hexAWNeighbor c e)) / 2


end
end StatMech.Universality
