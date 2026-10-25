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
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSpinGauge


namespace StatMech.FrontierA

open StatMech.Onsager


noncomputable def triangularTorusSpinVertexGauge
    (L : Nat) (a b : Fin 2) (p : ZMod L × ZMod L) : Complex :=
  ons_spinPhase L a ^ (-(p.1.val : Int)) *
    ons_spinPhase L b ^ (-(p.2.val : Int))

end StatMech.FrontierA
