/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorContinuation
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGraphTransition


namespace StatMech.FrontierA

open SimpleGraph StatMech.Onsager

def triangularTorusDartToGraphDart
    (L : Nat) [Fact (2 < L)] :
    triangularTorusDart L → (triangularTorusGraph L).Dart :=
  fun d => ⟨(d.1, d.1 - triangularTorusDirectionStep L d.2),
    triangularTorusDart_adj L d.1 d.2⟩

end StatMech.FrontierA
