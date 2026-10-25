/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorContinuation
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGraphTransition.Part4


namespace StatMech.FrontierA

open SimpleGraph StatMech.Onsager

def triangularTorusDartReverse (L : Nat) :
    triangularTorusDart L → triangularTorusDart L :=
  fun d =>
    (d.1 - triangularTorusDirectionStep L d.2,
      triangularTorusDirectionReverse d.2)

end StatMech.FrontierA
