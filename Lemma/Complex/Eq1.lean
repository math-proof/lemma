import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma norm_le_one_of_forall_pow_norm_sub_one_lt (u : ℂ) (hu : ∀ n : ℕ, ‖u ^ n - 1‖ < 1) : ‖u‖ ≤ 1 := by
  by_contra h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) (not_le.mp h)
  have h1 := hu n
  have h2 : ‖u‖ ^ n - 1 ≤ ‖u ^ n - 1‖ := by
    simpa [norm_pow, norm_one] using norm_sub_norm_le (u ^ n) 1
  linarith

private lemma eq_zero_of_abs_le_pi_of_forall_cos_pos (t : ℝ) (htpi : |t| ≤ Real.pi) (h : ∀ n : ℕ, 0 < Real.cos (n * t)) : t = 0 := by
  by_contra hne
  have ht : 0 < |t| := abs_pos.mpr hne
  have hcos : ∀ n : ℕ, 0 < Real.cos (n * |t|) := by
    intro n
    have hn := h n
    rwa [← Real.cos_abs, abs_mul, Nat.abs_cast] at hn
  have hex : ∃ n : ℕ, Real.pi / 2 ≤ n * |t| := by
    obtain ⟨n, hn⟩ := exists_nat_ge (Real.pi / 2 / |t|)
    exact ⟨n, (div_le_iff₀ ht).mp hn⟩
  classical
  have hspec : Real.pi / 2 ≤ (Nat.find hex : ℝ) * |t| := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    obtain h0 | h0 := Nat.eq_zero_or_pos (Nat.find hex)
    ·
      exfalso
      rw [h0] at hspec
      simp [zero_mul] at hspec
      linarith [Real.pi_pos]
    ·
      apply h0
  have hprev : ¬ Real.pi / 2 ≤ ((Nat.find hex - 1 : ℕ) : ℝ) * |t| := Nat.find_min hex (Nat.sub_lt hpos Nat.one_pos)
  rw [Nat.cast_sub hpos, Nat.cast_one] at hprev
  have hlt : (Nat.find hex : ℝ) * |t| < Real.pi / 2 + |t| := by
    have := not_le.mp hprev
    nlinarith
  have hle : (Nat.find hex : ℝ) * |t| ≤ Real.pi + Real.pi / 2 := by linarith
  have := Real.cos_nonpos_of_pi_div_two_le_of_le hspec hle
  linarith [hcos (Nat.find hex)]

/--
[LanglandsTunnell_Converse_units_eq_one_of_forall_zpow_norm_sub_one_lt](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LanglandsTunnell_Converse_units_eq_one_of_forall_zpow_norm_sub_one_lt.lean)
-/
@[path]
private lemma main
  (z : Units ℂ)
  (hz : ∀ n : ℤ, ‖((z ^ n : Units ℂ) : ℂ) - 1‖ < 1) :
  -- imply
  z = 1 := by
  -- proof
  have hpow : ∀ n : ℤ, ‖(z : ℂ) ^ n - 1‖ < 1 := fun n => by
    simpa [Units.val_zpow_eq_zpow_val] using hz n
  have hz1 : ‖(z : ℂ)‖ ≤ 1 := norm_le_one_of_forall_pow_norm_sub_one_lt _ fun n => by
    simpa [zpow_natCast] using hpow n
  have hz2 : ‖((z : ℂ)⁻¹)‖ ≤ 1 := norm_le_one_of_forall_pow_norm_sub_one_lt _ fun n => by
    have h := hpow (-(n : ℤ))
    rwa [zpow_neg, zpow_natCast, ← inv_pow] at h
  have hzpos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
  have hnorm : ‖(z : ℂ)‖ = 1 := by
    rw [norm_inv, inv_le_one₀ hzpos] at hz2
    apply le_antisymm hz1 hz2
  have hcos : ∀ n : ℕ, 0 < Real.cos (n * Complex.arg (z : ℂ)) := by
    intro n
    have h1 := hpow n
    rw [zpow_natCast] at h1
    have hre : ((z : ℂ) ^ n).re = Real.cos (n * Complex.arg (z : ℂ)) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (z : ℂ)]
      rw [hnorm, Complex.ofReal_one, one_mul, ← Complex.exp_nat_mul, ← mul_assoc]
      have hc : ((n : ℂ) * ((Complex.arg (z : ℂ) : ℝ) : ℂ)) = (((n : ℝ) * Complex.arg (z : ℂ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hc, Complex.exp_ofReal_mul_I_re]
    have h2 : |((z : ℂ) ^ n - 1).re| ≤ ‖(z : ℂ) ^ n - 1‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.one_re, hre] at h2
    have h3 := (abs_lt.mp (lt_of_le_of_lt h2 h1)).1
    linarith
  have harg : Complex.arg (z : ℂ) = 0 := eq_zero_of_abs_le_pi_of_forall_cos_pos _ (Complex.abs_arg_le_pi _) hcos
  have h := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
  rw [hnorm, harg] at h
  simpa using h.symm


-- created on 2026-10-20
