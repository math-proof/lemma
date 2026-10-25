/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceConnected.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoopHeight
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceNoLoop


namespace StatMech.FrontierD

noncomputable section

open Filter Topology


noncomputable def fkRectZeroTurnSelectedPrimalTouchedCrossing
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
    FKRectRawPrimalHorizontalCrossingComponent R omega :=
  (fkRectZeroTurnPrimalTouchedCrossings_nonempty_of_avoidsRowSeam
    R omega C hC).choose

end
end StatMech.FrontierD
