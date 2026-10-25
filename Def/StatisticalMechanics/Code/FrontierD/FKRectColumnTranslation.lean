/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectColumnTranslate (R : FKRectTorus) (s : Int)
    (x : Fin R.width) : Fin R.width :=
  fkRectIntModFin R.width_pos ((x.val : Int) + s)

end
end StatMech.FrontierD
