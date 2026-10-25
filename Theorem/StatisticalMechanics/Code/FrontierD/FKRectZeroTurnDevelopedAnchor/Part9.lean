/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part8
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectMedialDartAbovePrimalVertex_label
    (R : FKRectTorus) (x : R.Vertex) :
    fkRectMedialDartPrimalLabel R
      (fkRectMedialDartAbovePrimalVertex R x) = x := by
  unfold fkRectMedialDartAbovePrimalVertex
  let y : R.Vertex := (x.1, finitePeriodicSucc R.height_pos x.2)
  by_cases hy : Even y.2.val
  · simp [fkRectMedialEastPrimal, y, hy,
      svCyclicPred_finitePeriodicSucc]
  · simp [fkRectMedialWestPrimal, y, hy,
      svCyclicPred_finitePeriodicSucc]


end
end StatMech.FrontierD
