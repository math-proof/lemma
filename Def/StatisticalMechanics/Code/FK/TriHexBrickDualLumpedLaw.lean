/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexBrickDualLumpedLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexBrickDualBundles
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualLumpedLaw.Part3
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice Ising Walls BeffaraDC

open StatMech.FrontierD

noncomputable section

def triHexBrickDualLumpedParam (N m : Nat) (p : Real)
    (a : Sym2 (kwg_Face (triHexPlanarFiniteStarPlanar m))) : Real :=
  if a ∈ Set.range (ocd_innerEdge (triHexBrickInnerFaceMap N m)) then p
  else if a ∈ (triHexBrickFullDualGraph m).edgeSet then
    indexedEffectiveParam
      (kwg_dualEnds (triHexPlanarFiniteStarPlanar m)) p a
  else 1 / 2

end
end StatMech.FK.PeriodicPlanar
