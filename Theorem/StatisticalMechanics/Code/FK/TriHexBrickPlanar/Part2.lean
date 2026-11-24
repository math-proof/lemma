module
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
public import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
public import Def.StatisticalMechanics.Code.FK.TriHexBrickPlanar.Part2
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


@[simp] theorem triHexPlanarFiniteStarPlanar_graph (n : Nat) :
    (triHexPlanarFiniteStarPlanar n).G =
      triHexPlanarFiniteStarGraph n := rfl

end StatMech.FK.PeriodicPlanar
