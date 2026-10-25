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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part3
open MeasureTheory StatMech.Lattice SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectVertexBoxEmbedding (R : FKRectTorus) :
    R.Vertex → FK.boxVerts 2 (R.width + R.height) :=
  fun x => ⟨fkRectVertexSquareSite R x,
    fkRectVertexSquareSite_mem_box R x⟩

end
end StatMech.FrontierD
