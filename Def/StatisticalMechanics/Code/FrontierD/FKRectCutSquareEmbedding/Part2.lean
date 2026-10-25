/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part5
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part2
open MeasureTheory StatMech.Lattice SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectVertexSquareSite (R : FKRectTorus) (x : R.Vertex) : Site 2 :=
  fkRectSquareSiteOfPair (fkRectVertexSquarePoint R x)

end
end StatMech.FrontierD
