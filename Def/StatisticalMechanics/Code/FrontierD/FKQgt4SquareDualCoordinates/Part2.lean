/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualDomination
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareAnchoredShell.Part4
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualCoordinates
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

open StatMech.Universality

noncomputable section

def fkSquareActiveRestrictLE {R N : Nat} (hRN : R ≤ N)
    (rho : ConfigSpace (FK.boxGraph 2 N).edgeSet) :
    ConfigSpace (FK.boxGraph 2 R).edgeSet :=
  restrictActive (FK.boxGraph 2 R)
    (FK.boxRestrictLE 2 hRN (extendActive (FK.boxGraph 2 N) rho))

end
end StatMech.FrontierD
