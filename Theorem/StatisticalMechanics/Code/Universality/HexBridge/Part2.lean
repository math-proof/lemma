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
import Def.StatisticalMechanics.Code.Universality.HexBridge


namespace StatMech.Universality

open Filter Topology

open scoped Topology BigOperators


namespace HexColumn

variable {T : ℕ} {χ : ℝ}


theorem colSum_crit_summable (C : HexColumn T χ) : Summable (fun w => χ ^ C.len w) :=
  C.crit_summable


theorem colSum_summable (C : HexColumn T χ) {x : ℝ} (hx : 0 ≤ x) (hχ : 0 < χ)
    (hxχ : x ≤ χ) : Summable (fun w => x ^ C.len w) :=
  (C.crit_summable.mul_left ((x / χ) ^ T)).of_nonneg_of_le
    (fun w => by positivity)
    (fun w => hexBr_pow_decay x χ T (C.len w) hx hχ hxχ (C.len_ge w))


theorem colSum_le_decay (C : HexColumn T χ) {x : ℝ} (hx : 0 ≤ x) (hχ : 0 < χ)
    (hxχ : x ≤ χ) :
    C.colSum x ≤ (x / χ) ^ T * C.colSum χ := by
  have hsx := C.colSum_summable hx hχ hxχ
  unfold colSum
  calc (∑' w, x ^ C.len w)
      ≤ ∑' w, (x / χ) ^ T * χ ^ C.len w :=
        hsx.tsum_mono (C.crit_summable.mul_left _)
          (fun w => hexBr_pow_decay x χ T (C.len w) hx hχ hxχ (C.len_ge w))
    _ = (x / χ) ^ T * ∑' w, χ ^ C.len w := tsum_mul_left


theorem colSum_le_pow (C : HexColumn T χ) {x : ℝ} (hx : 0 ≤ x) (hχ : 0 < χ)
    (hxχ : x ≤ χ) :
    C.colSum x ≤ (x / χ) ^ T := by
  have hpow_nn : (0 : ℝ) ≤ (x / χ) ^ T := by positivity
  calc C.colSum x ≤ (x / χ) ^ T * C.colSum χ := C.colSum_le_decay hx hχ hxχ
    _ ≤ (x / χ) ^ T * 1 := by
        apply mul_le_mul_of_nonneg_left C.crit_le_one hpow_nn
    _ = (x / χ) ^ T := mul_one _


theorem colSum_nonneg (C : HexColumn T χ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ C.colSum x := by
  unfold colSum
  exact tsum_nonneg (fun w => by positivity)

end HexColumn
end StatMech.Universality
