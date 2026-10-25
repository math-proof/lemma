/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualLumpedLaw.Part3
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomainActive
open Finset Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

noncomputable section

def fkSquareDualInnerActiveRestrict
    {N m : Nat} (hNm : N < m)
    (rho : ConfigSpace (fkSquareBoxFullDualGraph m).edgeSet) :
    ConfigSpace (FK.boxGraph 2 N).edgeSet :=
  ocd_innerRestrictActive (FK.boxGraph 2 N)
    (fkSquareBoxFullDualGraph m) (fkSquareBox_innerFaceMap N m)
    (fkSquareBox_innerFaceMap_adjMatch hNm) rho


end
end StatMech.FrontierD
