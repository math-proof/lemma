/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.CorrelationLength.Part3
import Def.StatisticalMechanics.Code.Exact3D.RG


namespace StatMech

namespace Exact3D

namespace BlockScale

theorem toReal_gt_one (s : BlockScale) : 1 < s.toReal := by
  unfold toReal
  exact_mod_cast s.one_lt

theorem toReal_pos (s : BlockScale) : 0 < s.toReal :=
  lt_trans zero_lt_one s.toReal_gt_one


theorem L_ne_zero (s : BlockScale) : s.L ≠ 0 :=
  Nat.ne_of_gt (lt_trans Nat.zero_lt_one s.one_lt)


theorem tendsto_mul_atTop (s : BlockScale) :
    Filter.Tendsto (fun n : ℕ => s.L * n) Filter.atTop Filter.atTop :=
  tendsto_nat_mul_atTop s.L_ne_zero

end BlockScale


theorem HasInverseCorrelationLength.rescale_blockScale {ι : Type*}
    {M : CriticalModel ι} {β : ℝ} {origin : ι} {ray : ℕ → ι} {m : ℝ}
    (scale : BlockScale)
    (h : HasInverseCorrelationLength M β origin ray m) :
    HasInverseCorrelationLength M β origin (fun n => ray (scale.L * n))
      (scale.toReal * m) := by
  simpa [BlockScale.toReal] using h.rescale_nat scale.L_ne_zero


theorem HasCorrelationLength.rescale_blockScale {ι : Type*}
    {M : CriticalModel ι} {β : ℝ} {origin : ι} {ray : ℕ → ι} {ξ : ℝ}
    (scale : BlockScale)
    (h : HasCorrelationLength M β origin ray ξ) :
    HasCorrelationLength M β origin (fun n => ray (scale.L * n))
      (ξ / scale.toReal) := by
  simpa [BlockScale.toReal] using h.rescale_nat scale.L_ne_zero


end Exact3D
end StatMech
