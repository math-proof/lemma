/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part5


namespace StatMech.Universality

theorem rlcScaleOneRouteClass_zero_fixed (omega : RlcScaleOneEdgeConfig)
    (h : rlcScaleOneRouteClass omega = 0) : omega 6 = false := by
  cases h6 : omega 6 <;> cases h11 : omega 11 <;>
    cases h7 : omega 7 <;> cases h9 : omega 9 <;>
    simp_all [rlcScaleOneRouteClass]

theorem rlcScaleOneRouteClass_one_fixed (omega : RlcScaleOneEdgeConfig)
    (h : rlcScaleOneRouteClass omega = 1) :
    omega 6 = true ∧ omega 11 = false ∧ omega 7 = false := by
  cases h6 : omega 6 <;> cases h11 : omega 11 <;>
    cases h7 : omega 7 <;> cases h9 : omega 9 <;>
    simp_all [rlcScaleOneRouteClass]

theorem rlcScaleOneRouteClass_two_fixed (omega : RlcScaleOneEdgeConfig)
    (h : rlcScaleOneRouteClass omega = 2) :
    omega 6 = true ∧ omega 11 = true ∧ omega 7 = false ∧
      omega 9 = false := by
  cases h6 : omega 6 <;> cases h11 : omega 11 <;>
    cases h7 : omega 7 <;> cases h9 : omega 9 <;>
    simp_all [rlcScaleOneRouteClass]

theorem rlcScaleOneRouteClass_three_fixed (omega : RlcScaleOneEdgeConfig)
    (h : rlcScaleOneRouteClass omega = 3) :
    omega 6 = true ∧ (omega 11 = true ∨ omega 7 = true) ∧
      (omega 9 = true ∨ omega 7 = true) := by
  cases h6 : omega 6 <;> cases h11 : omega 11 <;>
    cases h7 : omega 7 <;> cases h9 : omega 9 <;>
    simp_all [rlcScaleOneRouteClass]

end StatMech.Universality
