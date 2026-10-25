/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAmplitudeExchange


namespace StatMech.FrontierD

noncomputable section

theorem sum_perm_eq_zero_of_mul_neg {n : ℕ} (τ : Equiv.Perm (Fin n))
    (f : Equiv.Perm (Fin n) → ℂ) (hmul : ∀ σ, f (σ * τ) = -f σ) :
    ∑ σ, f σ = 0 := by
  let e : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) := Equiv.mulRight τ
  have hreindex : (∑ σ, f σ) = ∑ σ, f (σ * τ) := by
    simpa [e] using (Equiv.sum_comp e f).symm
  have hneg : (∑ σ, f (σ * τ)) = -(∑ σ, f σ) := by
    calc
      (∑ σ, f (σ * τ)) = ∑ σ, -f σ := by
        apply Finset.sum_congr rfl
        intro σ _
        exact hmul σ
      _ = -(∑ σ, f σ) := by rw [Finset.sum_neg_distrib]
  have hself : (∑ σ, f σ) = -(∑ σ, f σ) := hreindex.trans hneg
  linear_combination (1 / 2 : ℂ) * hself


theorem sum_perm_eq_zero_of_swap_neg {n : ℕ} (i j : Fin n)
    (f : Equiv.Perm (Fin n) → ℂ)
    (hswap : ∀ σ, f (σ * Equiv.swap i j) = -f σ) :
    ∑ σ, f σ = 0 := by
  exact sum_perm_eq_zero_of_mul_neg (Equiv.swap i j) f hswap


theorem sixVertexBetheM_mul_L_sub_one {c : ℝ} (hc : 2 < c)
    {z w : ℂ} (hz : z ≠ 1) (hw : w ≠ 1) :
    sixVertexBetheM c z * sixVertexBetheL c w - 1 =
      -((c : ℂ) ^ 2) * sixVertexBethePairFactor c w z /
        ((1 - z) * (1 - w)) := by
  have hcz : (c : ℂ) ^ 2 ≠ 0 := by
    norm_cast
    positivity
  have hz' : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have hw' : 1 - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  unfold sixVertexBetheM sixVertexBetheL sixVertexBethePairFactor
    sixVertexDelta
  push_cast
  field_simp
  ring


theorem sixVertexBethe_geometricInterval
    (c : ℝ) {z : ℂ} (hz : z ≠ 1) {a b : ℕ} (hab : a < b) :
    z ^ a + (c : ℂ) ^ 2 * (∑ y ∈ Finset.Ioo a b, z ^ y) + z ^ b =
      sixVertexBetheL c z * z ^ a + sixVertexBetheM c z * z ^ b := by
  rw [← Finset.Ico_succ_left_eq_Ioo]
  rw [Nat.succ_eq_succ]
  rw [geom_sum_Ico' hz (Nat.succ_le_iff.mpr hab)]
  unfold sixVertexBetheL sixVertexBetheM
  simp only [pow_succ]
  field_simp [sub_ne_zero.mpr (Ne.symm hz)]
  ring


theorem sixVertexBethe_relaxedWordExpansion
    (c : ℝ) {n : ℕ} (z : Fin n → ℂ) (a b : Fin n → ℕ)
    (hz : ∀ k, z k ≠ 1) (hab : ∀ k, a k < b k) :
    (∏ k, ((z k) ^ (a k) + (c : ℂ) ^ 2 *
        (∑ y ∈ Finset.Ioo (a k) (b k), (z k) ^ y) + (z k) ^ (b k))) =
      ∑ w : Finset (Fin n),
        (∏ k ∈ w, sixVertexBetheL c (z k) * (z k) ^ (a k)) *
          ∏ k ∈ wᶜ, sixVertexBetheM c (z k) * (z k) ^ (b k) := by
  calc
    (∏ k, ((z k) ^ (a k) + (c : ℂ) ^ 2 *
        (∑ y ∈ Finset.Ioo (a k) (b k), (z k) ^ y) + (z k) ^ (b k))) =
      ∏ k, (sixVertexBetheL c (z k) * (z k) ^ (a k) +
        sixVertexBetheM c (z k) * (z k) ^ (b k)) := by
      apply Finset.prod_congr rfl
      intro k _
      exact sixVertexBethe_geometricInterval c (hz k) (hab k)
    _ = _ := Fintype.prod_add _ _


end
end StatMech.FrontierD
