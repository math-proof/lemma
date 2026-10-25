/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualLumpedLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualBundles.Part2
import Theorem.StatisticalMechanics.Code.FK.IndexedEdgeLumping.Part2
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualLumpedLaw
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section

def fkSquareDualLumpedParam (N m : Nat) (p : Real)
    (a : Sym2 (kwg_Face (fkSquareBoxPlanar m))) : Real :=
  if a ∈ Set.range (ocd_innerEdge (fkSquareBox_innerFaceMap N m)) then p
  else if a ∈ (fkSquareBoxFullDualGraph m).edgeSet then
    indexedEffectiveParam (kwg_dualEnds (fkSquareBoxPlanar m)) p a
  else 1 / 2

end
end StatMech.FrontierD
