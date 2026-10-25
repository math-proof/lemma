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
import Structure.StatisticalMechanics.Code.Universality.HexLiteralCriticalDivergence.Part2


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlcd_side_limit_forces_literal_divergence
    {a : ℂ} {h0 : ℤ} {tau : ℕ → ℝ}
    (S : HexLiteralSideLimits a h0 tau)
    (hpos : ∃ T, 1 ≤ T ∧ 0 < tau T) :
    ¬ Summable (fun ts : List ℤ => hexSAWwt a h0 hexChiE ts) := by
  rintro hwalk
  obtain ⟨T, _, hTpos⟩ := hpos
  have hfib : Summable (S.fibers.columnEmb T).fiberSum :=
    (S.fibers.columnEmb T).fiberSum_summable hwalk
  have hzero := hfib.tendsto_atTop_zero
  have : tau T = 0 := tendsto_nhds_unique (S.tendsto_tau T) hzero
  exact (ne_of_gt hTpos) this


end StatMech.Universality
