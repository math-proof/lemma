/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexBoundary.Part4
import Def.StatisticalMechanics.Code.Universality.HexContourDecomp


namespace StatMech.Universality

open Complex

open scoped BigOperators


namespace HexSide

variable {V : Type*} [DecidableEq V] {D : HexDomain V}


theorem incSum_eq_dir_mul_fSum (s : HexSide D) :
    s.incSum = s.dir * s.fSum := by
  unfold incSum fSum HexDomain.incTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [s.dirEq e he]


theorem proj_of_tilt (θ : ℝ) (c : ℂ) :
    (Complex.I * Complex.exp ((-θ : ℝ) * Complex.I))
        * (Complex.exp ((θ : ℝ) * Complex.I) * ((Real.cos θ : ℂ) * c))
      = Complex.I * ((Real.cos θ : ℂ) * c) := by
  have : Complex.exp ((-θ : ℝ) * Complex.I) * Complex.exp ((θ : ℝ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    rw [show ((-θ : ℝ) : ℂ) * Complex.I + (θ : ℝ) * Complex.I = 0 by push_cast; ring]
    exact Complex.exp_zero
  calc
    (Complex.I * Complex.exp ((-θ : ℝ) * Complex.I))
        * (Complex.exp ((θ : ℝ) * Complex.I) * ((Real.cos θ : ℂ) * c))
      = Complex.I * ((Real.cos θ : ℂ) * c)
          * (Complex.exp ((-θ : ℝ) * Complex.I) * Complex.exp ((θ : ℝ) * Complex.I)) := by ring
    _ = Complex.I * ((Real.cos θ : ℂ) * c) * 1 := by rw [this]
    _ = Complex.I * ((Real.cos θ : ℂ) * c) := by ring

end HexSide
end StatMech.Universality
