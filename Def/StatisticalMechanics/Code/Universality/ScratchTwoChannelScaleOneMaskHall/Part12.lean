/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part8


namespace StatMech.Universality

def rlcScaleOneRoutedFailureConfig
    (rho : RlcScaleOneRoutedFailure) : RlcScaleOneEdgeConfig :=
  match rho with
  | Sum.inl a => a.1
  | Sum.inr (Sum.inl b) => b.1
  | Sum.inr (Sum.inr (Sum.inl c)) => c.1
  | Sum.inr (Sum.inr (Sum.inr d)) => d.1

def rlcScaleOneFailureClassify
    (rho : RlcScaleOneConnectorFailure) : RlcScaleOneRoutedFailure :=
  if h0 : rlcScaleOneRouteClass rho.1 = 0 then
    Sum.inl ⟨rho.1, h0, rlcScaleOneFailure_fiberA rho h0⟩
  else if h1 : rlcScaleOneRouteClass rho.1 = 1 then
    Sum.inr (Sum.inl ⟨rho.1, h1, rlcScaleOneFailure_fiberB rho h1⟩)
  else if h2 : rlcScaleOneRouteClass rho.1 = 2 then
    Sum.inr (Sum.inr (Sum.inl
      ⟨rho.1, h2, rlcScaleOneFailure_fiberC rho h2⟩))
  else
    have h3 : rlcScaleOneRouteClass rho.1 = 3 := by
      apply Fin.eq_of_val_eq
      have hlt := (rlcScaleOneRouteClass rho.1).isLt
      have hn0 : (rlcScaleOneRouteClass rho.1).val ≠ 0 := by
        intro hval
        exact h0 (Fin.eq_of_val_eq hval)
      have hn1 : (rlcScaleOneRouteClass rho.1).val ≠ 1 := by
        intro hval
        exact h1 (Fin.eq_of_val_eq hval)
      have hn2 : (rlcScaleOneRouteClass rho.1).val ≠ 2 := by
        intro hval
        exact h2 (Fin.eq_of_val_eq hval)
      omega
    Sum.inr (Sum.inr (Sum.inr
      ⟨rho.1, h3, rlcScaleOneFailure_fiberD rho h3⟩))

end StatMech.Universality
