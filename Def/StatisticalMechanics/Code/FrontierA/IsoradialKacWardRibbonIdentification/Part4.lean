/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanProduct
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part5


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


namespace CriticalKacWardRibbonCoefficientIdentification

noncomputable def toRibbonExpansion
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex) (thetaEdge : E -> Real)
    (exceptional : V -> Bool)
    (I : CriticalKacWardRibbonCoefficientIdentification
      R character kacWard thetaEdge exceptional) :
    CriticalKacWardRibbonExpansion
      R character kacWard thetaEdge exceptional where
  expansion := by
    change (1 - kacWard).det =
      criticalKacWardRibbonPrefactor thetaEdge exceptional * _
    exact I.expansion R character kacWard thetaEdge exceptional

end CriticalKacWardRibbonCoefficientIdentification
end StatMech.FrontierA
