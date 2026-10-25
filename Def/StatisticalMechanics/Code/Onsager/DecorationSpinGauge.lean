/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalMiddle.Part3
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopHomology.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge


namespace StatMech.Onsager

open BigOperators

noncomputable def ons_spinVertexGauge
    (L : ℕ) (a b : Fin 2) (site : ZMod L × ZMod L) : ℂ :=
  ons_spinPhase L a ^ (site.1.val : ℤ) *
    ons_spinPhase L b ^ (site.2.val : ℤ)

noncomputable def ons_spinDartSeamSign
    {L : ℕ} (a b : Fin 2) (d : ons_Dart L) : ℂ :=
  (-1 : ℂ) ^ ((a.val : ℤ) * ons_xWrapSign d +
    (b.val : ℤ) * ons_yWrapSign d)

end StatMech.Onsager
