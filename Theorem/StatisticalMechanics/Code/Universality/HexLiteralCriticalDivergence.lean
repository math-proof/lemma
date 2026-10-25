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


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlcd_not_summable_iff (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    (¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n)) ↔
      ¬ Summable (fun ts : List ℤ => hexSAWwt a h0 x ts) := by
  simpa only [hlc_sawCountR] using
    (not_congr (hlc_summable_iff a h0 hx)).symm


theorem hlcd_not_summable_of_literal (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (hdiv : ¬ Summable (fun ts : List ℤ => hexSAWwt a h0 x ts)) :
    ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) :=
  (hlcd_not_summable_iff a h0 hx).2 hdiv


end StatMech.Universality
