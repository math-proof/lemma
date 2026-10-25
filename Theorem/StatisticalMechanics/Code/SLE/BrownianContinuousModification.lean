/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianContinuousModification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianDyadicApproximation.Part2
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


namespace StatMech.SLE

theorem brownianDyadicApproxIndex_eq_add (N L n : Nat) {t : Real}
    (hNL : N <= L) (htLower : -(N : Real) <= t) :
    brownianDyadicApproxIndex L n t =
      brownianDyadicApproxIndex N n t +
        (L - N) * brownianDyadicDenominator n := by
  have hx : 0 <= (t + N) * brownianDyadicDenominator n :=
    mul_nonneg (by linarith) (by positivity)
  have harg : (t + L) * brownianDyadicDenominator n =
      (t + N) * brownianDyadicDenominator n +
        (((L - N) * brownianDyadicDenominator n : Nat) : Real) := by
    push_cast
    have hLN : (L : Real) = N + (L - N : Nat) := by
      exact_mod_cast (Nat.add_sub_of_le hNL).symm
    rw [hLN]
    ring
  unfold brownianDyadicApproxIndex
  rw [harg, Nat.floor_add_natCast hx]


theorem brownianDyadicApproxPoint_eq_of_le (N L n : Nat) {t : Real}
    (hNL : N <= L) (htLower : -(N : Real) <= t) :
    brownianDyadicApproxPoint L n t = brownianDyadicApproxPoint N n t := by
  unfold brownianDyadicApproxPoint brownianDyadicPoint
  rw [brownianDyadicApproxIndex_eq_add N L n hNL htLower]
  push_cast
  have hD : ((brownianDyadicDenominator n : Nat) : Real) ≠ 0 := by
    exact_mod_cast (brownianDyadicDenominator_pos n).ne'
  have hLN : (L : Real) = N + (L - N : Nat) := by
    exact_mod_cast (Nat.add_sub_of_le hNL).symm
  rw [hLN]
  field_simp [hD]
  ring


theorem brownianDyadicLimit_eq_of_le (omega : Real -> Real)
    (N L : Nat) {t : Real} (hNL : N <= L) (htLower : -(N : Real) <= t) :
    brownianDyadicLimit L t omega = brownianDyadicLimit N t omega := by
  unfold brownianDyadicLimit
  congr 1
  funext n
  rw [brownianDyadicApproxPoint_eq_of_le N L n hNL htLower]


end StatMech.SLE
