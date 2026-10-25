/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRankOneWindingTail
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryVerticalFlux.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierPatternCost
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectCutMedialColumn (R : FKRectTorus)
    (x : Fin R.width) (b : Bool) : Fin R.medialTorus.width :=
  (fkRectMedialVertexOfEdge R
    (b, (x, ⟨0, R.height_pos⟩))).1

end
end StatMech.FrontierD
