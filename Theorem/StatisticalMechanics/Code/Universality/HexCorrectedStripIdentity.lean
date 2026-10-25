/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripIdentity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripStartReturn
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part6


namespace StatMech.Universality

open Complex HexWalk

noncomputable section

theorem hexCS_startReturnLaw (T L : ℕ) (hT : 0 < T) :
    HexCSStartReturnLaw T L hT := by
  intro ts hadm
  exact hexCS_endpoint_return_eq_nil T L hT ts hadm


end
end StatMech.Universality
