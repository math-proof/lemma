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
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSpinGauge.Part3


namespace StatMech.FrontierA

open StatMech.Onsager


noncomputable def triangularTorusSeamKWMatrix
    (L : Nat) (t1 t2 t3 rho : Complex) (a b : Fin 2) :
    Matrix (triangularTorusDart L) (triangularTorusDart L) Complex :=
  fun d e =>
    if (d.1.1 - e.1.1, d.1.2 - e.1.2) =
        triangularTorusDirectionStep L d.2 then
      triangularTorusDirectionWeight t1 t2 t3 d.2 *
        (triangularTorusSpinDartSeamSign L a b d *
          triangularKacWardTurnMatrix rho d.2 e.2)
    else 0


noncomputable def triangularTorusSpinDartGauge
    (L : Nat) (a b : Fin 2) (d : triangularTorusDart L) : Complex :=
  (triangularTorusSpinVertexGauge L a b d.1)⁻¹

end StatMech.FrontierA
