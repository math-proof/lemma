/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHammersleyWelshClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Def.StatisticalMechanics.Code.Universality.HexHammersleyWelshClose


namespace StatMech.Universality

open scoped BigOperators


theorem hhw_hexColumnOfBoundary_colSum (a : ℂ) (h0 : ℤ) (T : ℕ)
    (mem : List ℤ → Prop) (hreach lam tau hlam htau hbdry) (y : ℝ) :
    (hhw_hexColumnOfBoundary a h0 T mem hreach lam tau hlam htau hbdry).colSum y
      = ∑' w : {ts // mem ts}, y ^ (HexWalk.ofTurns a h0 w.1).numVertices := rfl


theorem hhw_hexColumnOfBoundary_critLeOne (a : ℂ) (h0 : ℤ) (T : ℕ)
    (mem : List ℤ → Prop) (hreach lam tau hlam htau hbdry) :
    ((hhw_hexColumnOfBoundary a h0 T mem hreach lam tau hlam htau hbdry).colSum hexChiE) ≤ 1 :=
  (hhw_hexColumnOfBoundary a h0 T mem hreach lam tau hlam htau hbdry).crit_le_one


theorem hhw_hexColumnOfBoundary_nonvacuous (a : ℂ) (h0 : ℤ) (T : ℕ)
    (hreach : ∀ ts, (fun _ : List ℤ => False) ts →
      ∃ v ∈ (HexWalk.ofTurns a h0 ts).vertices, a.re + T ≤ v.re) :
    ∃ lam tau : Finset {ts : List ℤ // (fun _ : List ℤ => False) ts} → ℝ,
      (∀ s, 0 ≤ lam s) ∧ (∀ s, 0 ≤ tau s) ∧
      (∀ s : Finset {ts : List ℤ // (fun _ : List ℤ => False) ts},
        hexCl * lam s + hexCt * tau s
          + (∑ w ∈ s, hexChiE ^ (HexWalk.ofTurns a h0 w.1).numVertices) = 1) := by
  refine ⟨fun _ => hexCl⁻¹, fun _ => 0,
    fun _ => le_of_lt (inv_pos.mpr hexCl_pos), fun _ => le_refl 0, ?_⟩
  intro s
  
  have hempty : s = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨ts, hts⟩ _
    exact hts
  subst hempty
  simp only [Finset.sum_empty, mul_zero, add_zero]
  rw [mul_inv_cancel₀ (ne_of_gt hexCl_pos)]

end StatMech.Universality
