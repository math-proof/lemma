module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceConnected.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoopHeight
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part9
public import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceNoLoop.Part2


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


noncomputable def fkRectZeroTurnSelectedHorizontalCutEdge
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (hC : ¬ FKRectZeroTurnUsesPrimalTouchedCrossings R omega C) :
    FKRectHorizontalCutEdge R :=
  ⟨(exists_fkRectHorizontalCutEdge_mem_remainderBoundaryCycleWalk
      R omega C hC).choose,
    (exists_fkRectHorizontalCutEdge_mem_remainderBoundaryCycleWalk
      R omega C hC).choose_spec.1⟩

end
end StatMech.FrontierD
