/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareWiredPhaseTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareDualInfiniteDomination
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceDualFrame.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareInverseDualPercolation
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityBoxInfluence
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareWiredPhaseTransport
open Filter Finset MeasureTheory Set SimpleGraph Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

open StatMech.Percolation StatMech.Universality

open StatMech.FK.PeriodicPlanar

noncomputable section

def fkSquareActiveConnToBoundaryEvent
    (N : Nat) (x : FK.boxVerts 2 N) :
    Set (ConfigSpace (FK.boxGraph 2 N).edgeSet) :=
  {rho | IsingFK.ConnToBdry (FK.boxGraph 2 N) (FK.boxBoundary 2 N)
    (extendActive (FK.boxGraph 2 N) rho) x}

end
end StatMech.FrontierD
