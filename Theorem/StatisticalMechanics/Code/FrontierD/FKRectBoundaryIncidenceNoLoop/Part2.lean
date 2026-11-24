module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceConnected.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoopHeight
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part9
public import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceNoLoop.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceNoLoop.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

open Filter Topology


theorem fkRectZeroTurnSelectedPrimalTouchedCrossing_mem
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
    fkRectZeroTurnSelectedPrimalTouchedCrossing R omega C hC ∈
      fkRectZeroTurnPrimalTouchedCrossings R omega C :=
  (fkRectZeroTurnPrimalTouchedCrossings_nonempty_of_avoidsRowSeam
    R omega C hC).choose_spec


end
end StatMech.FrontierD
