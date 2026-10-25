/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickPlanar.Part2
import Def.StatisticalMechanics.Code.FK.TriHexBrickFaces.Part2
open SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls


theorem triHexPlanarFiniteStarFace_eq_right (n : Nat) (t : Site 2) :
    triHexPlanarFiniteStarFace n t =
      BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar n)
        (hexagonalBrickFaceRight t) :=
  triHexPlanarFiniteStar_pfdFace_left_eq_right n t


end StatMech.FK.PeriodicPlanar
