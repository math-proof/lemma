/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSpinGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGraphTransition.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusHomology.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part5


namespace StatMech.FrontierA

open StatMech.Onsager


def triangularTorusXMovementDirection : Fin 6 -> Fin 4 :=
  ![2, 0, 1, 1, 2, 0]


def triangularTorusYMovementDirection : Fin 6 -> Fin 4 :=
  ![0, 0, 3, 1, 3, 1]

def triangularTorusXMovementDart (L : Nat) :
    triangularTorusDart L -> ons_Dart L :=
  fun d => (d.1, triangularTorusXMovementDirection d.2)

def triangularTorusYMovementDart (L : Nat) :
    triangularTorusDart L -> ons_Dart L :=
  fun d => (d.1, triangularTorusYMovementDirection d.2)

end StatMech.FrontierA
