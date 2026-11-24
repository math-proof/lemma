module
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
public import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
open SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickPlanar.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open Lattice BeffaraDC


def hexagonalBrickVertex (u : HexVertex) : Site 2 :=
  if u.2 then
    ![2 * u.1 0 + u.1 1 - 2, -u.1 1 + 1]
  else
    ![2 * u.1 0 + u.1 1, -u.1 1]

end StatMech.FK.PeriodicPlanar
