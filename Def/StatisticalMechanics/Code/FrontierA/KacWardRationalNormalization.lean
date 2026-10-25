/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRationalNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalPhaseReduction.Part2


namespace StatMech.FrontierA

open scoped BigOperators


def kwRatCommonDenominator {n : ℕ} (q : Fin n → ℚ × ℚ) : ℕ :=
  ∏ i : Fin n, (q i).1.den * (q i).2.den

end StatMech.FrontierA
