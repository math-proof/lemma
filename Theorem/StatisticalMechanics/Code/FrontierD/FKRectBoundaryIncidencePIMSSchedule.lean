/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSSchedule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceScheduledCapstone
import Mathlib.Data.Nat.Choose.Bounds
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule
open Filter Topology MeasureTheory


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPIMSDecayDepth_spec
    {a : Real} {p : Nat → Real} (hp_one : ∀ k, p k ≤ 1) (k : Nat) :
    p k ≤ a ^ fkRectPIMSDecayDepth a p k := by
  unfold fkRectPIMSDecayDepth
  apply Nat.findGreatest_spec (P := fun d => p k ≤ a ^ d) (Nat.zero_le k)
  simpa using hp_one k


theorem tendsto_fkRectPIMSDecayDepth_atTop
    {a : Real} (ha : 0 < a) {p : Nat → Real}
    (hp : Tendsto p atTop (nhds 0)) :
    Tendsto (fkRectPIMSDecayDepth a p) atTop atTop := by
  refine tendsto_atTop.2 (fun N => ?_)
  have haN : 0 < a ^ N := pow_pos ha N
  have hpN : ∀ᶠ k in atTop, p k < a ^ N :=
    (tendsto_order.1 hp).2 _ haN
  filter_upwards [hpN, eventually_ge_atTop N] with k hpk hk
  exact Nat.le_findGreatest hk hpk.le


end
end StatMech.FrontierD
