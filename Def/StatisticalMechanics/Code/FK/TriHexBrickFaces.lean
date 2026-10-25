/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickPlanar.Part2
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls


def hexagonalBrickFaceLeft (t : Site 2) : Site 2 :=
  ![2 * t 0 + t 1 - 2, -t 1]


def hexagonalBrickFaceRight (t : Site 2) : Site 2 :=
  ![2 * t 0 + t 1 - 1, -t 1]

end StatMech.FK.PeriodicPlanar
