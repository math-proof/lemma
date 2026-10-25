/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointAggregation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Def.StatisticalMechanics.Code.Universality.HexEndpointAggregation


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

theorem hexEndpointSAWwt_nonneg
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) (ts : List ℤ) :
    0 ≤ hexEndpointSAWwt a h0 x ts := by
  unfold hexEndpointSAWwt
  split
  · exact pow_nonneg hx _
  · exact le_rfl


end
end StatMech.Universality
