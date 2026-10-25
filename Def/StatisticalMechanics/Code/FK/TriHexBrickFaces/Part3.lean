/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickPlanar.Part2
import Theorem.StatisticalMechanics.Code.FK.TriHexBrickFaces.Part2
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls


def triHexSpokeFace1 (z : Site 2) (i : Fin 3) : Site 2 :=
  ![z, z, z + hexagonalStep 0] i


def triHexSpokeFace2 (z : Site 2) (i : Fin 3) : Site 2 :=
  ![z + hexagonalStep 0, z + hexagonalStep 1,
    z + hexagonalStep 1] i


def triHexBrickSpokeFlank1 (z : Site 2) (i : Fin 3) : Site 2 :=
  ![hexagonalBrickFaceRight z,
    hexagonalBrickFaceRight z,
    hexagonalBrickFaceLeft (z + hexagonalStep 0)] i


def triHexBrickSpokeFlank2 (z : Site 2) (i : Fin 3) : Site 2 :=
  ![hexagonalBrickFaceLeft (z + hexagonalStep 0),
    hexagonalBrickFaceLeft (z + hexagonalStep 1),
    hexagonalBrickFaceRight (z + hexagonalStep 1)] i

end StatMech.FK.PeriodicPlanar
