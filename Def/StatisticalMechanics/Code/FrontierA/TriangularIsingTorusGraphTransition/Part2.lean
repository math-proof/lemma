/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorContinuation
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGraphTransition.Part2


namespace StatMech.FrontierA

open SimpleGraph StatMech.Onsager

noncomputable def triangularTorusDartEquiv
    (L : Nat) [Fact (2 < L)] :
    triangularTorusDart L ≃ (triangularTorusGraph L).Dart :=
  Equiv.ofBijective (triangularTorusDartToGraphDart L)
    (triangularTorusDartToGraphDart_bijective L)

end StatMech.FrontierA
