/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCriticalDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointAggregation.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Def.StatisticalMechanics.Code.Universality.HexEndpointCriticalDivergence


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hecd_columnSum_nonneg
    (a : ℂ) (h0 : ℤ) (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ) (v : ℕ) :
    0 ≤ hecd_columnSum a h0 P scale v := by
  unfold hecd_columnSum HexColumnEmb.fiberSum
  exact tsum_nonneg
    (fun _ => hexEndpointSAWwt_nonneg a h0 (le_of_lt hexChiE_pos) _)

theorem hecd_columnSum_summable
    (a : ℂ) (h0 : ℤ) (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ)
    (hwalk : Summable (hexEndpointSAWwt a h0 hexChiE)) :
    Summable (hecd_columnSum a h0 P scale) :=
  (hexEndpointColumnEmbOfPred a h0 (le_of_lt hexChiE_pos) P scale).fiberSum_summable
    hwalk


end
end StatMech.Universality
