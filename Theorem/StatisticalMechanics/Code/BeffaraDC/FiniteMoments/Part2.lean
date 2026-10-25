/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.RussoHamming.Part2
import Def.StatisticalMechanics.Code.BeffaraDC.FiniteMoments


namespace StatMech

namespace BeffaraDC

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem hammingMoment_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (d : ℕ) : 0 ≤ hammingMoment p A d :=
  expect_nonneg hp0 hp1 (fun ω => by positivity)


theorem hammingMoment_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (d : ℕ) :
    hammingMoment p A d ≤ (Fintype.card E : ℝ) ^ d := by
  unfold hammingMoment
  refine expect_le_const hp0 hp1 (fun ω => ?_)
  exact pow_le_pow_left₀ (by positivity) (hammingToSet_real_le_card A ω) d


theorem hammingMoment_lt_top {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (d : ℕ) :
    hammingMoment p A d < (Fintype.card E : ℝ) ^ d + 1 :=
  lt_of_le_of_lt (hammingMoment_le hp0 hp1 A d) (by linarith)


theorem hammingMoment_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (hcard : Fintype.card E ≤ 1) (d : ℕ) :
    hammingMoment p A d ≤ 1 := by
  refine (hammingMoment_le hp0 hp1 A d).trans ?_
  have : (Fintype.card E : ℝ) ≤ 1 := by exact_mod_cast hcard
  calc (Fintype.card E : ℝ) ^ d ≤ (1 : ℝ) ^ d :=
        pow_le_pow_left₀ (by positivity) this d
    _ = 1 := one_pow d


end BeffaraDC
end StatMech
