/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickFreeCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualCoordinates.Part4
import Theorem.StatisticalMechanics.Code.FK.FreeNestedDecreasing
import Theorem.StatisticalMechanics.Code.FK.TriHexBrickFreeCofinal
open Filter Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.FrontierD

noncomputable section

def triHexPlanarFiniteStarToHexBufferedLE
    {r n : Nat} (hrn : r + 2 ≤ n) :
    TriHexPlanarFiniteStarVertex r ↪ hexagonal.BufferedVertex n :=
  (triHexPlanarFiniteStarToHexBuffered r).trans
    (hexagonal.bufferedVertexInclLE hrn)

end
end StatMech.FK.PeriodicPlanar
