/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Abbrev.StatisticalMechanics.Code.Universality.HexGenuineStripStartGeometry


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


def hexGenuineStripIncA : HexIncidence (Fin 1) := ⟨0, 0⟩


def hexGenuineStripIncU : HexIncidence (Fin 1) := ⟨0, 1⟩


def hexGenuineStripIncTp : HexIncidence (Fin 1) := ⟨0, 2⟩


def hexGenuineStripHeading (_ : Fin 1) (j : Fin 3) : ℤ :=
  match j with
  | 0 => 4
  | 1 => 0
  | 2 => 2

end StatMech.Universality
