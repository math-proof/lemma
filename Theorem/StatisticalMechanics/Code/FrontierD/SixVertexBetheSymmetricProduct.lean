/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricProduct
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

theorem sixVertexBethePhase_norm (p : ℝ) :
    ‖sixVertexBethePhase p‖ = 1 := by
  simp [sixVertexBethePhase, Complex.norm_exp]

theorem sixVertexBethePhase_neg (p : ℝ) :
    sixVertexBethePhase (-p) = star (sixVertexBethePhase p) := by
  unfold sixVertexBethePhase
  simpa using Complex.exp_conj (Complex.I * (p : ℂ))


theorem sixVertexBetheM_phase_neg (c p : ℝ) :
    sixVertexBetheM c (sixVertexBethePhase (-p)) =
      star (sixVertexBetheM c (sixVertexBethePhase p)) := by
  rw [sixVertexBethePhase_neg]
  simp [sixVertexBetheM]


theorem sixVertexBetheL_phase_eq_conj_M (c p : ℝ) :
    sixVertexBetheL c (sixVertexBethePhase p) =
      star (sixVertexBetheM c (sixVertexBethePhase p)) := by
  let z := sixVertexBethePhase p
  have hn : ‖z‖ = 1 := sixVertexBethePhase_norm p
  have hz : z ≠ 0 := norm_ne_zero_iff.mp (by simp [hn])
  change sixVertexBetheL c z = (starRingEnd ℂ) (sixVertexBetheM c z)
  by_cases h1 : z = 1
  · simp [sixVertexBetheL, sixVertexBetheM, h1]
  · simp only [sixVertexBetheM, map_sub, map_one, map_div₀, map_pow,
      Complex.conj_ofReal]
    rw [← Complex.inv_eq_conj hn]
    simp only [sixVertexBetheL]
    have hden : 1 - z⁻¹ = (z - 1) / z := by
      field_simp [hz]
    rw [hden, div_div_eq_mul_div]
    rw [show z - 1 = -(1 - z) by ring, div_neg]
    ring

theorem sixVertexBetheM_symmetric_pair (c p : ℝ) :
    sixVertexBetheM c (sixVertexBethePhase p) *
        sixVertexBetheM c (sixVertexBethePhase (-p)) =
      (Complex.normSq (sixVertexBetheM c (sixVertexBethePhase p)) : ℂ) := by
  rw [sixVertexBetheM_phase_neg]
  exact Complex.mul_conj _

theorem sixVertexBetheL_symmetric_pair (c p : ℝ) :
    sixVertexBetheL c (sixVertexBethePhase p) *
        sixVertexBetheL c (sixVertexBethePhase (-p)) =
      (Complex.normSq (sixVertexBetheM c (sixVertexBethePhase p)) : ℂ) := by
  rw [sixVertexBetheL_phase_eq_conj_M,
    sixVertexBetheL_phase_eq_conj_M, sixVertexBetheM_phase_neg]
  simp only [star_star]
  rw [mul_comm]
  exact Complex.mul_conj _


end StatMech.FrontierD
