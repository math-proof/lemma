/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalMiddle.Part3
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopHomology.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part4


namespace StatMech.Onsager

open BigOperators

noncomputable def ons_decMiddleStateGauge
    (L : ℕ) (a b : Fin 2) (site : ZMod L × ZMod L) :
    ons_Dart L ⊕ Fin 2 → ℂ
  | .inl d => ons_spinVertexGauge L a b d.1
  | .inr _ => ons_spinVertexGauge L a b site

end StatMech.Onsager
