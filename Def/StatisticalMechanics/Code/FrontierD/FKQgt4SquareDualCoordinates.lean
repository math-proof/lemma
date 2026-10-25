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
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

open StatMech.Universality

noncomputable section

def fkSquareFaceDualInnerActive (N : Nat)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    ConfigSpace (FK.boxGraph 2 N).edgeSet :=
  fun a => fci_faceDualConfig omega (FK.edgeIncl 2 N a.1)


end
end StatMech.FrontierD
