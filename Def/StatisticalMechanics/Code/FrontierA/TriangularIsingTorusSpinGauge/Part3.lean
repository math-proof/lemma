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
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSpinGauge.Part2


namespace StatMech.FrontierA

open StatMech.Onsager


noncomputable def triangularTorusSpinDartSeamSign
    (L : Nat) (a b : Fin 2) (d : triangularTorusDart L) : Complex :=
  (-1 : Complex) ^
    (-((a.val : Int) *
        ons_xWrapSign (triangularTorusXMovementDart L d)) -
      (b.val : Int) *
        ons_yWrapSign (triangularTorusYMovementDart L d))

end StatMech.FrontierA
