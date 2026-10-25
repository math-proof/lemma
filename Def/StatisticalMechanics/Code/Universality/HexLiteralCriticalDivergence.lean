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
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCriticalDivergence


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


noncomputable def hlcd_columnSum (a : ℂ) (h0 : ℤ) (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ) (v : ℕ) : ℝ :=
  (hexColumnEmbOfPred a h0 (le_of_lt hexChiE_pos) P scale).fiberSum v


end StatMech.Universality
