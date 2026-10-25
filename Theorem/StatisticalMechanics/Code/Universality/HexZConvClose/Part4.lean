/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Def.StatisticalMechanics.Code.Universality.HexZConvClose.Part5


namespace StatMech.Universality

open scoped BigOperators

open HexWalk


theorem hzc_wtγ_nn (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x) (N : ℕ)
    (d : hzc_Dn a h0 N) : 0 ≤ hzc_wtγ a h0 x N d :=
  hexSAWwt_nonneg a h0 hx d.1


theorem hzc_partial_eq_attach (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) :
    ∑ d : hzc_Dn a h0 N, hzc_wtγ a h0 x N d
      = ∑ n ∈ Finset.range N, (hzc_sawCount a h0 n : ℝ) * x ^ n := by
  rw [show (∑ d : hzc_Dn a h0 N, hzc_wtγ a h0 x N d)
        = ∑ ts ∈ hzc_truncFinset a h0 N, hexSAWwt a h0 x ts from
      Finset.sum_coe_sort (hzc_truncFinset a h0 N) (hexSAWwt a h0 x)]
  exact hzc_partial_eq a h0 x N


theorem hzc_nil_isLegalSAW (a : ℂ) (h0 : ℤ) : (ofTurns a h0 []).IsLegalSAW := by
  refine ⟨?_, ?_⟩
  · intro t ht; simp only [ofTurns_turns, List.not_mem_nil] at ht
  · unfold IsSAW vertices
    simp only [ofTurns_startMid, ofTurns_h0, ofTurns_turns, verticesAux_nil]
    exact List.nodup_singleton _


theorem hzc_nil_mem_truncFinset (a : ℂ) (h0 : ℤ) {N : ℕ} (hN : 2 ≤ N) :
    [] ∈ hzc_truncFinset a h0 N := by
  rw [hzc_mem_truncFinset]
  refine ⟨hzc_nil_isLegalSAW a h0, ?_⟩
  have : (ofTurns a h0 []).numVertices = 1 := by
    rw [numVertices_eq]; rfl
  omega


theorem hzc_sawCount_one_pos (a : ℂ) (h0 : ℤ) : 1 ≤ hzc_sawCount a h0 1 := by
  classical
  unfold hzc_sawCount
  rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  push Not
  refine ⟨[], hzc_nil_mem_truncFinset a h0 (le_refl 2), ?_⟩
  rw [numVertices_eq]; rfl

end StatMech.Universality
