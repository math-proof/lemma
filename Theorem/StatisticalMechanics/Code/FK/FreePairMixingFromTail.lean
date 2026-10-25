/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePairMixingFromTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.FreeTailTriviality
import Theorem.StatisticalMechanics.Code.FK.FKTwoBoxDecoupling.Part2
import Theorem.StatisticalMechanics.Code.Foundations.BirkhoffErgodic
import Def.StatisticalMechanics.Code.FK.FreePairMixingFromTail
open MeasureTheory Set Filter Function
open scoped BigOperators ENNReal Topology


namespace StatMech

namespace FK

open ConfigSpace Lattice

variable {d : ℕ}


theorem freeAxisTranslationPower_eq_pow (hd : 1 ≤ d) (n : ℕ) :
    freeAxisTranslationPower hd n = (freeAxisTranslation hd) ^ n := by
  unfold freeAxisTranslationPower freeAxisTranslation
  rw [← ofAdd_nsmul]
  congr 1
  funext i
  simp only [Pi.smul_apply]
  by_cases hi : i = ⟨0, hd⟩ <;> simp [hi]

theorem shift_freeAxisTranslationPower (hd : 1 ≤ d) (n : ℕ) :
    (shift (freeAxisTranslationPower hd n) :
      ConfigSpace (Sym2 (Site d)) → ConfigSpace (Sym2 (Site d))) =
      (shift (freeAxisTranslation hd))^[n] := by
  rw [freeAxisTranslationPower_eq_pow]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, shift_mul, ih, Function.iterate_succ]

end FK
end StatMech
