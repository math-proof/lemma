/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareVerticalRate
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAllSectorWidthRate
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceRateCapstone
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSPhaseAssembly
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceSpectralSchedule
open Filter Topology MeasureTheory


namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation StatMech.BeffaraDC

noncomputable section

noncomputable def fkRectBalancedShareSpectralGap
    (q : Real) (r k : Nat) : Real :=
  Real.log (sixVertexWidthTopEigenvalue
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) -
    Real.log (sixVertexLambda (sixVertexFourWidth r (k + 1)) 0
      (sixVertexFourWidth_even r (k + 1)) (Nat.zero_le _)
      (fkQgt4SixVertexWeight q))


end
end StatMech.FrontierD
