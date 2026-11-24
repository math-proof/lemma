module
public import Theorem.StatisticalMechanics.Code.FK.TriHexBrickPlanar.Part2
public import Theorem.StatisticalMechanics.Code.FK.TriHexBrickFaces
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFaces.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls


noncomputable def triHexPlanarFiniteStarFace (n : Nat) (t : Site 2) :
    kwg_Face (triHexPlanarFiniteStarPlanar n) :=
  BeffaraDC.pfdFace (triHexPlanarFiniteStarPlanar n)
    (hexagonalBrickFaceLeft t)

end StatMech.FK.PeriodicPlanar
