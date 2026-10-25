/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleWeighted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.KWRectangleCritical.Part4
import Def.StatisticalMechanics.Code.Onsager.KWRectangleWeighted.Part2


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


theorem norm_ons_rectDartSignDefect
    (M N : Nat) (defect : ons_RectDart M N -> Prop)
    [DecidablePred defect] {q : Real} (hq : 0 <= q) (d : ons_RectDart M N) :
    ‖ons_rectDartSignDefect M N defect q d‖ = q := by
  unfold ons_rectDartSignDefect
  split_ifs <;> simp [Real.norm_eq_abs, abs_of_nonneg hq]


theorem ons_rectSignDefect_det_ratio_eq_walk_exp
    (M N : Nat) (defect : ons_RectDart M N -> Prop)
    [DecidablePred defect] (q : Real)
    (hq0 : 0 <= q) (hq : q < ons_signedLoopCriticalWeight) :
    (1 - ons_rectKWmatDartWeighted M N
          (ons_rectDartSignDefect M N defect q)).det /
        (1 - ons_rectKWmat M N (q : Complex)).det =
      Complex.exp
        (-(ons_rectWeightedWalkExponent M N
              (ons_rectDartSignDefect M N defect q) -
            ons_rectWeightedWalkExponent M N (fun _ => (q : Complex)))) := by
  have hdef := ons_rectKWmatDartWeighted_det_eq_walk_exp
    M N (ons_rectDartSignDefect M N defect q) q hq0 hq
    (fun d => (norm_ons_rectDartSignDefect M N defect hq0 d).le)
  have hplain := ons_rectKWmatDartWeighted_det_eq_walk_exp
    M N (fun _ => (q : Complex)) q hq0 hq (fun d => by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0])
  rw [ons_rectKWmatDartWeighted_const] at hplain
  rw [hdef, hplain, ← Complex.exp_sub]
  congr 1
  unfold ons_rectWeightedWalkExponent
  simp_rw [ons_rectKWmatDartWeighted_const]
  ring

end StatMech.Onsager
