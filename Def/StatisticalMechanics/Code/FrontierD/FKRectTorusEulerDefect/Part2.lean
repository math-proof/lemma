/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEulerDefect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEulerDefect
open scoped BigOperators


namespace StatMech.FrontierD

noncomputable section

def fkRectCriticalLoopNormalization (R : FKRectTorus) (q : Real) : Real :=
  (1 / (1 + Real.sqrt q)) ^ (2 * R.width * R.height) *
    Real.sqrt q ^ (R.width * R.height)


end
end StatMech.FrontierD
