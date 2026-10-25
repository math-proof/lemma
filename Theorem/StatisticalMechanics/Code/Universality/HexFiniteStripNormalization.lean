/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripBoundary.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBoundConcrete.Part4


namespace StatMech.Universality

open Complex HexWalk


theorem hexChi_ne_one : hexChi ≠ 1 := by
  intro h
  rw [hexChi_eq_sqrt] at h
  have hsqrt_pos : 0 < Real.sqrt (2 + Real.sqrt 2) := by
    rw [Real.sqrt_pos]
    positivity
  have hsqrt_one : Real.sqrt (2 + Real.sqrt 2) = 1 := by
    have hone : (1 : ℝ) = Real.sqrt (2 + Real.sqrt 2) :=
      (div_eq_one_iff_eq (ne_of_gt hsqrt_pos)).mp h
    exact hone.symm
  have hrad : (2 + Real.sqrt 2 : ℝ) = 1 := Real.sqrt_eq_one.mp hsqrt_one
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  linarith


theorem hexVBC_start_observable_eq_hexChi (a : ℂ) (h0 : ℤ) :
    parafObservable (hexVBCRegion a h0).inRegion a h0 a (5 / 8) hexChi
      = (hexChi : ℂ) := by
  have hobs := hexVBC_obs_p a h0
  rw [hexConcrete_p_eq a h0] at hobs
  rw [hobs]
  apply parafSummand_self
  rw [hexVBC_inRegion_iff]
  exact Or.inl rfl


theorem hexVBC_start_observable_ne_one (a : ℂ) (h0 : ℤ) :
    parafObservable (hexVBCRegion a h0).inRegion a h0 a (5 / 8) hexChi
      ≠ (1 : ℂ) := by
  rw [hexVBC_start_observable_eq_hexChi]
  exact fun h => hexChi_ne_one (Complex.ofReal_injective (by simpa using h))


end StatMech.Universality
