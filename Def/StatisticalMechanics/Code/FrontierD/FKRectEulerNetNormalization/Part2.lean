/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerNetIdentification
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorNormalization.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerNetNormalization.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def fkRectBalancedSectorShare (R : FKRectTorus) (q : Real) : Real :=
  fkRectBalancedSectorNormalization R q /
    fkRectAllSectorNormalization R q

end
end StatMech.FrontierD
