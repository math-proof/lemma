/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Def.StatisticalMechanics.Code.Universality.HexLiteralSubcritical.Part4


namespace StatMech.Universality

open HexWalk


theorem hls_card_encodedSix (a : ℂ) (h0 : ℤ) :
    (hls_encodedSix a h0).card = hlc_sawCount a h0 6 := by
  rw [hls_encodedSix, Finset.card_image_of_injective _ (hls_encode_injective a h0 6)]
  simp [hls_ExactSAW, hlc_card_sawFinset]


theorem hlc_sawCount_six_le (a : ℂ) (h0 : ℤ) :
    hlc_sawCount a h0 6 ≤ 62 := by
  let allowed : Finset (Fin 6 → Bool) :=
    (Finset.univ.erase hls_allTrue).erase hls_allFalse
  have hsub : hls_encodedSix a h0 ⊆ allowed := by
    intro f hf
    change f ∈ (Finset.univ.erase hls_allTrue).erase hls_allFalse
    rw [Finset.mem_erase, Finset.mem_erase]
    simp only [hls_encodedSix, Finset.mem_image] at hf
    obtain ⟨d, _, rfl⟩ := hf
    exact ⟨hls_encode_ne_allFalse a h0 d, hls_encode_ne_allTrue a h0 d,
      Finset.mem_univ _⟩
  have hdistinct : hls_allFalse ≠ hls_allTrue := by
    intro h
    have := congrFun h (0 : Fin 6)
    simp [hls_allFalse, hls_allTrue] at this
  have hfalseMem : hls_allFalse ∈ (Finset.univ : Finset (Fin 6 → Bool)).erase hls_allTrue :=
    Finset.mem_erase.mpr ⟨hdistinct, Finset.mem_univ _⟩
  have hallowed : allowed.card = 62 := by
    change ((Finset.univ : Finset (Fin 6 → Bool)).erase hls_allTrue |>.erase hls_allFalse).card = 62
    rw [Finset.card_erase_of_mem hfalseMem,
      Finset.card_erase_of_mem (Finset.mem_univ hls_allTrue), Finset.card_univ]
    simp
  calc
    hlc_sawCount a h0 6 = (hls_encodedSix a h0).card :=
      (hls_card_encodedSix a h0).symm
    _ ≤ allowed.card := Finset.card_le_card hsub
    _ = 62 := hallowed


theorem hlc_sawCount_six_blocks (a : ℂ) (h0 : ℤ) (q r : ℕ) :
    hlc_sawCount a h0 (6 * q + r) ≤ 62 ^ q * 2 ^ r := by
  induction q with
  | zero => simpa using hlc_sawCount_le_two_pow a h0 r
  | succ q ih =>
      calc
        hlc_sawCount a h0 (6 * (q + 1) + r)
            = hlc_sawCount a h0 (6 + (6 * q + r)) := by congr 1; omega
        _ ≤ hlc_sawCount a h0 6 * hlc_sawCount a h0 (6 * q + r) :=
          hlc_sawCount_submult a h0 6 (6 * q + r)
        _ ≤ 62 * (62 ^ q * 2 ^ r) :=
          Nat.mul_le_mul (hlc_sawCount_six_le a h0) ih
        _ = 62 ^ (q + 1) * 2 ^ r := by rw [pow_succ]; ring


theorem hlc_sawCountR_six_block_term_bound (a : ℂ) (h0 : ℤ) (x : ℝ)
    (hx : 0 ≤ x) (q r : ℕ) :
    hlc_sawCountR a h0 (6 * q + r) * x ^ (6 * q + r)
      ≤ ((2 : ℝ) * x) ^ r * ((62 : ℝ) * x ^ 6) ^ q := by
  have hc : hlc_sawCountR a h0 (6 * q + r) ≤
      (62 : ℝ) ^ q * (2 : ℝ) ^ r := by
    unfold hlc_sawCountR
    exact_mod_cast hlc_sawCount_six_blocks a h0 q r
  calc
    hlc_sawCountR a h0 (6 * q + r) * x ^ (6 * q + r)
        ≤ ((62 : ℝ) ^ q * (2 : ℝ) ^ r) * x ^ (6 * q + r) :=
          mul_le_mul_of_nonneg_right hc (pow_nonneg hx _)
    _ = ((2 : ℝ) * x) ^ r * ((62 : ℝ) * x ^ 6) ^ q := by
      rw [pow_add, pow_mul, mul_pow, mul_pow]
      ring


theorem hlc_sawCountR_summable_of_sixtyTwo_mul_pow_lt_one
    (a : ℂ) (h0 : ℤ) (x : ℝ) (hx : 0 ≤ x)
    (hcontract : (62 : ℝ) * x ^ 6 < 1) :
    Summable (fun n => hlc_sawCountR a h0 n * x ^ n) := by
  let ratio : ℝ := 62 * x ^ 6
  have hratio0 : 0 ≤ ratio := by
    dsimp [ratio]
    positivity
  have hratio : ‖ratio‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hratio0]
    exact hcontract
  have hrow : ∀ r : Fin 6, Summable (fun q : ℕ =>
      hlc_sawCountR a h0 (6 * q + r.1) * x ^ (6 * q + r.1)) := by
    intro r
    have hgeom : Summable (fun q : ℕ => ratio ^ q) :=
      summable_geometric_of_norm_lt_one hratio
    apply (hgeom.mul_left (((2 : ℝ) * x) ^ r.1)).of_nonneg_of_le
    · intro q
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)
    · intro q
      simpa only [ratio] using
        hlc_sawCountR_six_block_term_bound a h0 x hx q r.1
  let F : Fin 6 × ℕ → ℝ := fun p =>
    hlc_sawCountR a h0 (6 * p.2 + p.1.1) * x ^ (6 * p.2 + p.1.1)
  have hFnn : ∀ p, 0 ≤ F p := by
    intro p
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)
  have hF : Summable F := by
    apply (summable_prod_of_nonneg hFnn).2
    refine ⟨?_, summable_of_hasFiniteSupport (Set.toFinite _)⟩
    intro r
    exact hrow r
  let e : ℕ ≃ Fin 6 × ℕ :=
    (Nat.divModEquiv 6).trans (Equiv.prodComm ℕ (Fin 6))
  have hreindexed : Summable
      ((fun n => hlc_sawCountR a h0 n * x ^ n) ∘ e.symm) := by
    convert hF using 1
    funext p
    simp [F, e, Nat.divModEquiv_symm_apply]
    congr 2 <;> omega
  exact (e.symm.summable_iff).mp hreindexed


theorem hlc_sawCountR_summable_le_half (a : ℂ) (h0 : ℤ) (x : ℝ)
    (hx : 0 ≤ x) (hle : x ≤ 1 / 2) :
    Summable (fun n => hlc_sawCountR a h0 n * x ^ n) := by
  apply hlc_sawCountR_summable_of_sixtyTwo_mul_pow_lt_one a h0 x hx
  have hp : x ^ 6 ≤ ((1 : ℝ) / 2) ^ 6 := by gcongr
  norm_num at hp ⊢
  linarith


theorem hlc_sawCountR_summable_half (a : ℂ) (h0 : ℤ) :
    Summable (fun n => hlc_sawCountR a h0 n * ((1 : ℝ) / 2) ^ n) :=
  hlc_sawCountR_summable_le_half a h0 (1 / 2) (by norm_num) le_rfl


theorem hlc_sawCountR_summable_lt_half (a : ℂ) (h0 : ℤ) (x : ℝ)
    (hx : 0 ≤ x) (hlt : x < 1 / 2) :
    Summable (fun n => hlc_sawCountR a h0 n * x ^ n) := by
  have hratio : ‖(2 : ℝ) * x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hx)]
    linarith
  have hgeom : Summable (fun n : ℕ => ((2 : ℝ) * x) ^ n) :=
    summable_geometric_of_norm_lt_one hratio
  apply hgeom.of_nonneg_of_le
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx n)
  · intro n
    calc
      hlc_sawCountR a h0 n * x ^ n
          ≤ (2 : ℝ) ^ n * x ^ n :=
            mul_le_mul_of_nonneg_right (hlc_sawCountR_le_two_pow a h0 n)
              (pow_nonneg hx n)
      _ = ((2 : ℝ) * x) ^ n := (mul_pow 2 x n).symm


theorem hzc_sawCount_summable_lt_half (a : ℂ) (h0 : ℤ) (x : ℝ)
    (hx : 0 ≤ x) (hlt : x < 1 / 2) :
    Summable (fun n => (hzc_sawCount a h0 n : ℝ) * x ^ n) := by
  have hshift := (hlc_sawCountR_summable_lt_half a h0 x hx hlt).mul_left x
  have htail : Summable
      (fun n => (hzc_sawCount a h0 (n + 1) : ℝ) * x ^ (n + 1)) := by
    convert hshift using 1
    funext n
    simp only [hlc_sawCountR, hlc_sawCount, pow_succ]
    ring
  exact (summable_nat_add_iff 1).mp htail


theorem hls_half_lt_hexChiE : (1 : ℝ) / 2 < hexChiE := by
  have hsqrtTwo : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hsqrt : Real.sqrt (2 + Real.sqrt 2) < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    nlinarith
  unfold hexChiE
  exact one_div_lt_one_div_of_lt hex_sqrt_pos hsqrt


theorem hlc_sawCountR_subcritical_of_ge_half
    (a : ℂ) (h0 : ℤ)
    (hsharp : ∀ x : ℝ, 1 / 2 ≤ x → x < hexChiE →
      Summable (fun n => hlc_sawCountR a h0 n * x ^ n)) :
    ∀ x : ℝ, 0 ≤ x → x < hexChiE →
      Summable (fun n => hlc_sawCountR a h0 n * x ^ n) := by
  intro x hx hchi
  by_cases hhalf : x < 1 / 2
  · exact hlc_sawCountR_summable_lt_half a h0 x hx hhalf
  · exact hsharp x (le_of_not_gt hhalf) hchi


theorem hlc_sawCountR_subcritical_of_noncontracting
    (a : ℂ) (h0 : ℤ)
    (hsharp : ∀ x : ℝ, 0 ≤ x → 1 ≤ (62 : ℝ) * x ^ 6 → x < hexChiE →
      Summable (fun n => hlc_sawCountR a h0 n * x ^ n)) :
    ∀ x : ℝ, 0 ≤ x → x < hexChiE →
      Summable (fun n => hlc_sawCountR a h0 n * x ^ n) := by
  intro x hx hchi
  by_cases hcontract : (62 : ℝ) * x ^ 6 < 1
  · exact hlc_sawCountR_summable_of_sixtyTwo_mul_pow_lt_one
      a h0 x hx hcontract
  · exact hsharp x hx (le_of_not_gt hcontract) hchi

end StatMech.Universality
