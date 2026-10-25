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
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSpinGauge.Part2


namespace StatMech.FrontierA

open StatMech.Onsager


theorem triangularTorusSpinVertexGauge_ne_zero
    (L : Nat) (a b : Fin 2) (p : ZMod L × ZMod L) :
    triangularTorusSpinVertexGauge L a b p ≠ 0 := by
  exact mul_ne_zero
    (zpow_ne_zero _ (ons_spinPhase_ne_zero L a))
    (zpow_ne_zero _ (ons_spinPhase_ne_zero L b))


end StatMech.FrontierA
