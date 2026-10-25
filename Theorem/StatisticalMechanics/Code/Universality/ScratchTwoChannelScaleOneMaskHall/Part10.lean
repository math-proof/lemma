/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part13


namespace StatMech.Universality

theorem rlcScaleOneTaggedTarget_connectorSuccess
    (rho : RlcScaleOneRoutedFailure) :
    RlcScaleOneConnectorSuccess (rlcScaleOneTaggedTarget rho) := by
  have h := rlcScaleOneTaggedTarget_success rho
  simp only [rlcScaleOneFourRouteSuccess, Bool.or_eq_true,
    Bool.and_eq_true] at h
  rcases h with habc | h7168
  · rcases habc with hab | h224
    · rcases hab with h384 | h196
      · refine ⟨384, by decide, ?_⟩
        intro i hi
        rcases rlcScaleOneMask384_support i hi with rfl | rfl
        · exact h384.1
        · exact h384.2
      · refine ⟨196, by decide, ?_⟩
        intro i hi
        rcases rlcScaleOneMask196_support i hi with rfl | rfl | rfl
        · exact h196.1.1
        · exact h196.1.2
        · exact h196.2
    · refine ⟨224, by decide, ?_⟩
      intro i hi
      rcases rlcScaleOneMask224_support i hi with rfl | rfl | rfl
      · exact h224.1.1
      · exact h224.1.2
      · exact h224.2
  · refine ⟨7168, by decide, ?_⟩
    intro i hi
    rcases rlcScaleOneMask7168_support i hi with rfl | rfl | rfl
    · exact h7168.1.1
    · exact h7168.1.2
    · exact h7168.2

end StatMech.Universality
