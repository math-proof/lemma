/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part2
open scoped BigOperators


namespace StatMech.FrontierD

noncomputable section

def fkRectCriticalReducedZ (R : FKRectTorus) (q : Real) : Real :=
  ∑ omega : R.Configuration, fkRectCriticalReducedWeight R q omega

end
end StatMech.FrontierD
