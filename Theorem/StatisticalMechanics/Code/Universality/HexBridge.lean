/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame


namespace StatMech.Universality

open Filter Topology

open scoped Topology BigOperators


theorem hexBr_pow_decay (x χ : ℝ) (T n : ℕ) (hx : 0 ≤ x) (hχ : 0 < χ)
    (hxχ : x ≤ χ) (hn : T ≤ n) :
    x ^ n ≤ (x / χ) ^ T * χ ^ n := by
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hχ T)]
  rw [show n = T + (n - T) by omega, pow_add, pow_add]
  have key : x ^ (n - T) ≤ χ ^ (n - T) := pow_le_pow_left₀ hx hxχ _
  nlinarith [pow_nonneg hx T, pow_pos hχ T, pow_nonneg hx (n - T), pow_pos hχ (n - T),
    mul_le_mul_of_nonneg_left key (mul_nonneg (pow_nonneg hx T) (le_of_lt (pow_pos hχ T)))]


end StatMech.Universality
