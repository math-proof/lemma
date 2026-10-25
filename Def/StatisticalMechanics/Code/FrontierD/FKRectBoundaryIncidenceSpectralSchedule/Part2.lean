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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceSpectralSchedule.Part2
open Filter Topology MeasureTheory


namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation StatMech.BeffaraDC

noncomputable section

noncomputable def fkRectBalancedSectorNormalizationVerticalRate
    {q : Real} (hq : 4 < q) (r k : Nat) : Real :=
  fkRectAllSectorNormalizationVerticalRate hq r k +
    fkRectBalancedShareSpectralGap q r k


end
end StatMech.FrontierD
