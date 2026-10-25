/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareWiredPercolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareWiredPhaseTransport.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceDualPercolation
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangHarris.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.PercoItems
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareWiredPercolation
open Filter MeasureTheory Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising StatMech.FK

open StatMech.Percolation StatMech.Universality

open StatMech.FK.PeriodicPlanar

noncomputable section

def faceDualInfiniteAt (x : Site 2) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {omega | (cluster 2 (fci_faceDualConfig omega) x).Infinite}

end
end StatMech.FrontierD
