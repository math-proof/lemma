/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedWideCrossing
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedTranslation
open Set


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

def fkRectDevelopedSiteTranslate (u : Int × Int) (z : Site 2) : Site 2 :=
  ![z 0 + u.1, z 1 + u.2]

end
end StatMech.FrontierD
