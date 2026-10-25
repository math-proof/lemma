/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusLocalAngularSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusAngularSplit
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit.Part2


namespace StatMech.FrontierA

open SimpleGraph


def triangularTorusDirectionSignedAngle : Fin 6 -> Int :=
  ![4, 0, -2, 2, -3, 1]


noncomputable def triangularTorusLocalPortRoot
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (p : KWDartPort (triangularTorusGraph L)) : Complex :=
  rho ^ triangularTorusDirectionSignedAngle
    (triangularTorusGraphDartDirection L
      (kwDartOfPort (triangularTorusGraph L) p))

end StatMech.FrontierA
