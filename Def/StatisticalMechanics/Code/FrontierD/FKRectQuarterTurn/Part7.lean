/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part6
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

def fkRectQuarterTurnConfigurationEquiv
    (R : FKRectTorus) (hheight : 4 < R.height) :
    R.Configuration ≃ (fkRectQuarterTurnTorus R hheight).Configuration :=
  Equiv.arrowCongr (fkRectQuarterTurnEdgeEquiv R hheight)
    (Equiv.refl Bool)

end
end StatMech.FrontierD
