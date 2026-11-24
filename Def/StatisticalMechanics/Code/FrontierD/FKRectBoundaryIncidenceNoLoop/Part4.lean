module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceConnected.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoopHeight
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part9
public import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceNoLoop


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


noncomputable def fkRectZeroTurnSelectedPrimalOrRightBoundaryContact
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    FKRectZeroTurnPrimalOrRightBoundaryContact R omega := by
  classical
  exact if hC : FKRectZeroTurnUsesPrimalTouchedCrossings R omega C then
      Sum.inl (fkRectZeroTurnSelectedPrimalTouchedCrossing R omega C hC)
    else
      Sum.inr (fkRectZeroTurnSelectedDualRightBoundaryContact R omega C)

end
end StatMech.FrontierD
