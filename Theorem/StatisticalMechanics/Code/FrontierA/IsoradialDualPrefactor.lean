/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3


namespace StatMech.FrontierA

open Finset

open scoped BigOperators


theorem isoradial_dualCos_mul_criticalMu_inv
    (theta : Real) (htheta : 0 < theta)
    (htheta' : theta < Real.pi / 2) :
    (Real.cos (Real.pi / 2 - theta) : Complex) *
        (isoradialCriticalMu theta)⁻¹ =
      -Complex.I * (Real.cos theta : Complex) := by
  have hthetaPi : theta < Real.pi :=
    lt_trans htheta' (by nlinarith [Real.pi_pos])
  have hsin : Real.sin theta ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi htheta hthetaPi)
  have hedgeReal :
      Real.sin theta * (Real.tan theta)⁻¹ = Real.cos theta := by
    rw [Real.tan_eq_sin_div_cos, inv_div]
    field_simp
  have hedgeComplex :
      (Real.sin theta : Complex) * (Real.tan theta : Complex)⁻¹ =
        (Real.cos theta : Complex) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, hedgeReal]
  rw [Real.cos_pi_div_two_sub, isoradialCriticalMu,
    mul_inv_rev, Complex.inv_I]
  calc
    (Real.sin theta : Complex) *
        ((Real.tan theta : Complex)⁻¹ * -Complex.I) =
      ((Real.sin theta : Complex) *
        (Real.tan theta : Complex)⁻¹) * -Complex.I := by ring
    _ = (Real.cos theta : Complex) * -Complex.I := by
      rw [hedgeComplex]
    _ = -Complex.I * (Real.cos theta : Complex) := by ring

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [DecidableEq E] in

theorem prod_isoradial_dualCos_mul_criticalMu_inv
    (theta : E -> Real) (htheta : forall edge, 0 < theta edge)
    (htheta' : forall edge, theta edge < Real.pi / 2) :
    (∏ edge : E,
        (Real.cos (Real.pi / 2 - theta edge) : Complex)) *
        (∏ edge : E, isoradialCriticalMu (theta edge))⁻¹ =
      (-Complex.I) ^ Fintype.card E *
        ∏ edge : E, (Real.cos (theta edge) : Complex) := by
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  calc
    (∏ edge : E,
        (Real.cos (Real.pi / 2 - theta edge) : Complex) *
          (isoradialCriticalMu (theta edge))⁻¹) =
      ∏ edge : E,
        (-Complex.I) * (Real.cos (theta edge) : Complex) := by
      apply Finset.prod_congr rfl
      intro edge _
      exact isoradial_dualCos_mul_criticalMu_inv
        (theta edge) (htheta edge) (htheta' edge)
    _ = (-Complex.I) ^ Fintype.card E *
        ∏ edge : E, (Real.cos (theta edge) : Complex) := by
      rw [Finset.prod_mul_distrib]
      simp


end StatMech.FrontierA
