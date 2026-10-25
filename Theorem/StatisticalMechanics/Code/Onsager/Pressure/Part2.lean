/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/Pressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.HighTemp
import Def.StatisticalMechanics.Code.Onsager.Pressure
open scoped BigOperators
open Finset


namespace StatMech

namespace Onsager

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ons_pressureFinite_eq (β : ℝ) (hβ : 0 ≤ β) (hV : 0 < Fintype.card V) :
    ons_pressureFinite G β
      = Real.log 2
        + (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) * Real.log (Real.cosh β)
        + Real.log (ons_X G (Real.tanh β)) / (Fintype.card V : ℝ) := by
  unfold ons_pressureFinite
  rw [ons_hte G β]
  
  have h2 : ((2 : ℝ) ^ Fintype.card V) ≠ 0 := by positivity
  have hcosh : ((Real.cosh β) ^ G.edgeFinset.card) ≠ 0 :=
    pow_ne_zero _ (Real.cosh_pos β).ne'
  have htanh : 0 ≤ Real.tanh β := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hβ) (Real.cosh_pos β).le
  have hX : ons_X G (Real.tanh β) ≠ 0 :=
    (ons_X_pos G (Real.tanh β) htanh).ne'
  rw [Real.log_mul (mul_ne_zero h2 hcosh) hX, Real.log_mul h2 hcosh,
    Real.log_pow, Real.log_pow]
  have hVne : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hV.ne'
  field_simp

end Onsager
end StatMech
