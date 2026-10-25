/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareDualInfiniteDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualCoordinates.Part2
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part5
open Filter Finset MeasureTheory Set SimpleGraph Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

open StatMech.Universality

noncomputable section

def fkSquareFaceDualInnerEvent (N : Nat)
    (A : Set (ConfigSpace (FK.boxGraph 2 N).edgeSet)) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  fkSquareFaceDualInnerActive N ⁻¹' A

end
end StatMech.FrontierD
