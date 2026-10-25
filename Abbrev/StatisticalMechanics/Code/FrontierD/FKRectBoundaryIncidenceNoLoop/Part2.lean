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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceNoLoop.Part4


namespace StatMech.FrontierD

noncomputable section

open Filter Topology


abbrev FKRectHorizontalCutEdge (R : FKRectTorus) :=
  {a : R.EdgeIndex // a ∈ fkRectHorizontalCutEdges R}


end
end StatMech.FrontierD
