/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicControl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianKolmogorovTail
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Def.StatisticalMechanics.Code.SLE.BrownianDyadicControl
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


namespace StatMech.SLE

theorem brownianDyadicDenominator_pos (n : Nat) :
    0 < brownianDyadicDenominator n := by
  exact pow_pos (by norm_num) n

theorem brownianDyadicPoint_succ_sub (N n k : Nat) :
    brownianDyadicPoint N n (k + 1) - brownianDyadicPoint N n k =
      ((brownianDyadicDenominator n : Nat) : Real)⁻¹ := by
  have hdenom : Ne ((brownianDyadicDenominator n : Nat) : Real) 0 := by
    exact_mod_cast (brownianDyadicDenominator_pos n).ne'
  simp only [brownianDyadicPoint]
  field_simp
  norm_num

theorem edist_brownianDyadicPoint_succ (N n k : Nat) :
    edist (brownianDyadicPoint N n k) (brownianDyadicPoint N n (k + 1)) =
      ((brownianDyadicDenominator n : Nat) : ENNReal)⁻¹ := by
  rw [edist_dist, Real.dist_eq, abs_sub_comm,
    brownianDyadicPoint_succ_sub]
  rw [abs_of_nonneg]
  · simp [ENNReal.ofReal_inv_of_pos,
      Nat.cast_pos.mpr (brownianDyadicDenominator_pos n)]
  · positivity


end StatMech.SLE
