/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part4


namespace StatMech

namespace Exact3D

theorem FKXAxisConnectionTwoSidedSubexponentialBounds.tendsto_neg_log_div
    {conn Alo Ahi : ℕ → ℝ} {m : ℝ}
    (hbounds : FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m) :
    Filter.Tendsto (fun n : ℕ => -Real.log (conn n) / (n : ℝ))
      Filter.atTop (nhds m) :=
  tendsto_neg_log_div_of_eventually_between_prefactor_exp conn hbounds.1
    hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2.1 hbounds.2.2.2.2.1
    hbounds.2.2.2.2.2


theorem FKXAxisConnectionTwoSidedSubexponentialBounds.mass_eq_of_tendsto_neg_log_div
    {conn Alo Ahi : ℕ → ℝ} {m rate : ℝ}
    (hbounds : FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m)
    (hrate :
      Filter.Tendsto (fun n : ℕ => -Real.log (conn n) / (n : ℝ))
        Filter.atTop (nhds rate)) :
    m = rate :=
  tendsto_nhds_unique hbounds.tendsto_neg_log_div hrate


theorem FKXAxisConnectionTwoSidedSubexponentialBounds.congr_eventually
    {conn comparison Alo Ahi : ℕ → ℝ} {m : ℝ}
    (hbounds : FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m)
    (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
    FKXAxisConnectionTwoSidedSubexponentialBounds comparison Alo Ahi m := by
  refine ⟨hbounds.1, hbounds.2.1, hbounds.2.2.1, hbounds.2.2.2.1, ?_, ?_⟩
  · filter_upwards [hbounds.2.2.2.2.1, hEq] with n hlo hEq_n
    rw [hEq_n]
    exact hlo
  · filter_upwards [hbounds.2.2.2.2.2, hEq] with n hhi hEq_n
    rw [hEq_n]
    exact hhi


theorem FKXAxisConnectionTwoSidedSubexponentialBounds.congr_eventually_iff
    {conn comparison Alo Ahi : ℕ → ℝ} {m : ℝ}
    (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
    FKXAxisConnectionTwoSidedSubexponentialBounds conn Alo Ahi m ↔
      FKXAxisConnectionTwoSidedSubexponentialBounds comparison Alo Ahi m :=
  ⟨fun hbounds => hbounds.congr_eventually hEq,
    fun hbounds => hbounds.congr_eventually
      (hEq.mono fun _ hn => hn.symm)⟩


end Exact3D
end StatMech
