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
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualLumpedLaw.Part2
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section

def fkSquarePfdSupport (m : Nat)
    (omega : ConfigSpace (Sym2 (FK.boxVerts 2 m))) :
    ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet :=
  pfdIndexedSupportActive (fkSquareBoxPlanar m)
    (pfdEdgeComplement (fkSquareBoxPlanar m)
      (restrictActive (FK.boxGraph 2 m) omega))

end
end StatMech.FrontierD
