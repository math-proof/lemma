/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamBarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBarrierConnectionProduct
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier


namespace StatMech.FrontierD

noncomputable section

def fkRectAllButOneOpenSeamEvent (R : FKRectTorus)
    (gap : R.EdgeIndex) : Set R.Configuration :=
  fkRectIndexedPatternEvent R (fkRectHorizontalCutEdges R)
    (fkRectAllButOneOpenConfiguration R gap)

end
end StatMech.FrontierD
