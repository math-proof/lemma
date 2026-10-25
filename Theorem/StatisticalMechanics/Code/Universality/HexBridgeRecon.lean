/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRecon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7


namespace StatMech.Universality

open Filter Topology Complex

open scoped Topology BigOperators


lemma hexChiE_inv_pos : 0 < hexChiE⁻¹ := inv_pos.mpr hexChiE_pos


theorem hexCut_numVertices_sum (a₁ a₂ : ℂ) (h1 h2 : ℤ) (ts : List ℤ) (cp : ℕ)
    (hcp : cp ≤ ts.length) :
    (HexWalk.ofTurns a₁ h1 (ts.take cp)).numVertices
      + (HexWalk.ofTurns a₂ h2 (ts.drop cp)).numVertices
      = (HexWalk.ofTurns a₁ h1 ts).numVertices + 1 := by
  simp only [HexWalk.numVertices, HexWalk.ofTurns,
    List.length_take, List.length_drop, min_eq_left hcp]
  omega


theorem hexCut_pow_factor (a₁ a₂ : ℂ) (h1 h2 : ℤ) (x : ℝ) (hx : 0 < x)
    (ts : List ℤ) (cp : ℕ) (hcp : cp ≤ ts.length) :
    x ^ (HexWalk.ofTurns a₁ h1 ts).numVertices
      = x⁻¹ * (x ^ (HexWalk.ofTurns a₁ h1 (ts.take cp)).numVertices
                * x ^ (HexWalk.ofTurns a₂ h2 (ts.drop cp)).numVertices) := by
  have hsum := hexCut_numVertices_sum a₁ a₂ h1 h2 ts cp hcp
  rw [← pow_add, hsum, pow_succ,
    mul_comm (x ^ (HexWalk.ofTurns a₁ h1 ts).numVertices) x,
    ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hx), one_mul]


theorem hexHighestCut_weight_bound_literal (a a₂ : ℂ) (h0 h2 : ℤ) (x : ℝ) (hx : 0 < x)
    (ts : List ℤ) (cp : ℕ) (hcp : cp ≤ ts.length)
    (hleg1 : (HexWalk.ofTurns a h0 ts).IsLegalSAW →
      (HexWalk.ofTurns a h0 (ts.take cp)).IsLegalSAW)
    (hleg2 : (HexWalk.ofTurns a h0 ts).IsLegalSAW →
      (HexWalk.ofTurns a₂ h2 (ts.drop cp)).IsLegalSAW) :
    hexSAWwt a h0 x ts
      ≤ x⁻¹ * (hexSAWwt a h0 x (ts.take cp) * hexSAWwt a₂ h2 x (ts.drop cp)) := by
  by_cases hleg : (HexWalk.ofTurns a h0 ts).IsLegalSAW
  · rw [hexSAWwt_of_isLegalSAW a h0 x hleg,
        hexSAWwt_of_isLegalSAW a h0 x (hleg1 hleg),
        hexSAWwt_of_isLegalSAW a₂ h2 x (hleg2 hleg)]
    exact le_of_eq (hexCut_pow_factor a a₂ h0 h2 x hx ts cp hcp)
  · unfold hexSAWwt
    rw [if_neg hleg]
    exact mul_nonneg (by positivity)
      (mul_nonneg (hexSAWwt_nonneg a h0 (le_of_lt hx) (ts.take cp))
        (hexSAWwt_nonneg a₂ h2 (le_of_lt hx) (ts.drop cp)))


end StatMech.Universality
