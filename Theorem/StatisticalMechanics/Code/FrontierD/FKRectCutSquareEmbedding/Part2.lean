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
import Def.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding
open MeasureTheory StatMech.Lattice SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectSquareSiteOfPair_zero (p : Int × Int) :
    fkRectSquareSiteOfPair p 0 = p.1 := by
  simp [fkRectSquareSiteOfPair]

@[simp] theorem fkRectSquareSiteOfPair_one (p : Int × Int) :
    fkRectSquareSiteOfPair p 1 = p.2 := by
  simp [fkRectSquareSiteOfPair]

theorem fkRectSquareSiteOfPair_injective :
    Function.Injective fkRectSquareSiteOfPair := by
  intro p q hpq
  apply Prod.ext
  · simpa using congrFun hpq 0
  · simpa using congrFun hpq 1


end
end StatMech.FrontierD
