/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalMiddle.Part3
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopHomology.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part2


namespace StatMech.Onsager

open BigOperators

noncomputable def ons_spinSeamDecWeight
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ)
    (a b : Fin 2) (edge : ons_DecEdge L) : ℂ := by
  classical
  exact if h : ons_decIsExternal edge then
    ons_spinDartSeamSign a b (Classical.choose h) * decWeight edge
  else decWeight edge

end StatMech.Onsager
