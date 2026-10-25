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
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part4
open MeasureTheory StatMech.Lattice SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectPrimalUnexploredBoxEmbedding
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    FKRectPrimalUnexploredVertex R S eta →
      FK.boxVerts 2 (R.width + R.height) :=
  fun x => fkRectVertexBoxEmbedding R x.1

end
end StatMech.FrontierD
