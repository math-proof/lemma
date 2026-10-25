/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorContinuation
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGraphTransition.Part4


namespace StatMech.FrontierA

open SimpleGraph StatMech.Onsager

@[simp] theorem triangularTorusDartEquiv_reverse
    (L : Nat) [Fact (2 < L)] (d : triangularTorusDart L) :
    triangularTorusDartEquiv L (triangularTorusDartReverse L d) =
      (triangularTorusDartEquiv L d).symm := by
  apply Dart.ext
  apply Prod.ext
  · rfl
  · simp [triangularTorusDartEquiv, triangularTorusDartReverse,
      triangularTorusDartToGraphDart]

@[simp] theorem triangularKacWardTurnMatrix_reverse_zero
    (rho : Complex) (a : Fin 6) :
    triangularKacWardTurnMatrix rho a
      (triangularTorusDirectionReverse a) = 0 := by
  fin_cases a <;>
    simp [triangularKacWardTurnMatrix, triangularTorusDirectionReverse]


end StatMech.FrontierA
