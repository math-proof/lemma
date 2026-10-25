/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCoefficientAggregation.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexColumnMembershipClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralCriticalDivergence


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlcd_columnSum_nonneg (a : ℂ) (h0 : ℤ) (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ) (v : ℕ) :
    0 ≤ hlcd_columnSum a h0 P scale v := by
  unfold hlcd_columnSum HexColumnEmb.fiberSum
  exact tsum_nonneg (fun _ => hexSAWwt_nonneg a h0 (le_of_lt hexChiE_pos) _)


theorem hlcd_columnSum_summable (a : ℂ) (h0 : ℤ) (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ)
    (hwalk : Summable (fun ts : List ℤ => hexSAWwt a h0 hexChiE ts)) :
    Summable (hlcd_columnSum a h0 P scale) := by
  exact (hexColumnEmbOfPred a h0 (le_of_lt hexChiE_pos) P scale).fiberSum_summable hwalk


end StatMech.Universality
