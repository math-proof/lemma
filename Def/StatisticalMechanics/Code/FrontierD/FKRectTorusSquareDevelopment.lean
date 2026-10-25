/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4


namespace StatMech.FrontierD

noncomputable section

def fkRectSquareDevelopPoint (p : Int × Int) : Int × Int :=
  (p.1 + (p.2 + 1) / 2, p.1 - p.2 / 2)


end
end StatMech.FrontierD
