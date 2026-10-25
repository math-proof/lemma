import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Def.Analysis.MeasureTheory.Section_1_3_2.Part5
set_option doc.verso.suggestions false


/-- Binary digits are in \{0, 1\}. -/
lemma binaryDigit_le_one (x : ℝ) (j : ℕ) : binaryDigit x j ≤ 1 := by
  simp only [binaryDigit]
  split_ifs with h1 h2 <;> omega

/-- Binary digits of 0 are all 0. -/
lemma binaryDigit_zero (j : ℕ) : binaryDigit 0 j = 0 := by
  simp only [binaryDigit]
  have h0' : (0:ℝ) ∈ Set.Ico 0 1 := ⟨le_refl 0, by norm_num⟩
  rw [if_pos h0']
  simp [mul_zero]

/-- Binary digits of 1 are all 1. -/
lemma binaryDigit_one (j : ℕ) : binaryDigit 1 j = 1 := by
  simp only [binaryDigit, Set.mem_Ico, lt_self_iff_false, and_false, ↓reduceIte]

/-- The full sum ∑\_\{j≥0\} 2·(1/3)^(j+1) = 1. -/
lemma tsum_two_thirds_geometric : ∑' j : ℕ, (2:ℝ) * (1/3:ℝ)^(j + 1) = 1 := by
  have h1 : ∑' j : ℕ, (1/3:ℝ)^j = (1 - 1/3)⁻¹ :=
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)
  calc ∑' j : ℕ, (2:ℝ) * (1/3:ℝ)^(j + 1)
      = ∑' j : ℕ, (2/3:ℝ) * (1/3:ℝ)^j := by congr 1; ext j; ring
    _ = (2/3) * ∑' j : ℕ, (1/3:ℝ)^j := by rw [tsum_mul_left]
    _ = (2/3) * (1 - 1/3)⁻¹ := by rw [h1]
    _ = 1 := by norm_num

/-- The tail sum bound: ∑\_\{j≥k\} 2·(1/3)^(j+1) = (1/3)^k. -/
lemma tsum_tail_bound (k : ℕ) :
    ∑' j : ℕ, (2:ℝ) * (1/3:ℝ)^(k + j + 1) = (1/3:ℝ)^k := by
  have h1 : ∑' j : ℕ, (1/3:ℝ)^j = (1 - 1/3)⁻¹ :=
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)
  calc ∑' j : ℕ, (2:ℝ) * (1/3:ℝ)^(k + j + 1)
      = ∑' j : ℕ, (2:ℝ) * ((1/3:ℝ)^(k+1) * (1/3:ℝ)^j) := by
        congr 1; ext j; rw [← pow_add]; ring_nf
    _ = (2:ℝ) * (1/3:ℝ)^(k+1) * ∑' j : ℕ, (1/3:ℝ)^j := by
        rw [← tsum_mul_left]; congr 1; ext j; ring
    _ = (2:ℝ) * (1/3:ℝ)^(k+1) * (1 - 1/3)⁻¹ := by rw [h1]
    _ = (1/3:ℝ)^k := by field_simp; ring

/-- Helper: if ⌊2z⌋₊ % 2 = 1 then ⌊2z⌋₊ ≥ 2⌊z⌋₊ + 1 -/
lemma floor_two_mul_odd_ge {z : ℝ} (hz : 0 ≤ z) (hodd : ⌊2 * z⌋₊ % 2 = 1) :
    ⌊2 * z⌋₊ ≥ 2 * ⌊z⌋₊ + 1 := by
  have h_decomp : ⌊2 * z⌋₊ = 2 * (⌊2 * z⌋₊ / 2) + ⌊2 * z⌋₊ % 2 := (Nat.div_add_mod _ _).symm
  rw [hodd] at h_decomp
  have h_div : ⌊2 * z⌋₊ / 2 ≥ ⌊z⌋₊ := by
    have h1 : (2 * ⌊z⌋₊ : ℕ) ≤ ⌊2 * z⌋₊ := by
      have hfloor := Nat.floor_le hz
      apply Nat.le_floor
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      linarith
    rw [mul_comm] at h1
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr h1
  omega

/-- Helper: if ⌊2z⌋₊ % 2 = 0 then ⌊2z⌋₊ ≤ 2⌊z⌋₊ -/
lemma floor_two_mul_even_le {z : ℝ} (hz : 0 ≤ z) (heven : ⌊2 * z⌋₊ % 2 = 0) :
    ⌊2 * z⌋₊ ≤ 2 * ⌊z⌋₊ := by
  have h_decomp : ⌊2 * z⌋₊ = 2 * (⌊2 * z⌋₊ / 2) + ⌊2 * z⌋₊ % 2 := (Nat.div_add_mod _ _).symm
  rw [heven, add_zero] at h_decomp
  have h_div : ⌊2 * z⌋₊ / 2 ≤ ⌊z⌋₊ := by
    have h1 : ⌊2 * z⌋₊ < 2 * (⌊z⌋₊ + 1) := by
      have := Nat.lt_floor_add_one z
      have h2 : 2 * z < 2 * (⌊z⌋₊ + 1) := by linarith
      have h3 : (⌊2 * z⌋₊ : ℝ) ≤ 2 * z := Nat.floor_le (mul_nonneg (by norm_num) hz)
      have h4 : (⌊2 * z⌋₊ : ℝ) < 2 * (↑⌊z⌋₊ + 1) := lt_of_le_of_lt h3 h2
      have h5 : (⌊2 * z⌋₊ : ℝ) < 2 * ⌊z⌋₊ + 2 := by linarith
      exact_mod_cast h5
    omega
  omega

/-- Helper: equal mod 2 and equal ⌊z⌋ implies equal ⌊2z⌋ -/
lemma floor_two_mul_eq_of_mod_eq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h_floor : ⌊x⌋₊ = ⌊y⌋₊) (h_mod : ⌊2 * x⌋₊ % 2 = ⌊2 * y⌋₊ % 2) :
    ⌊2 * x⌋₊ = ⌊2 * y⌋₊ := by
  by_cases hxodd : ⌊2 * x⌋₊ % 2 = 1
  · have hyodd := h_mod ▸ hxodd
    have hx_ge := floor_two_mul_odd_ge hx hxodd
    have hy_ge := floor_two_mul_odd_ge hy hyodd
    have hx_lt : ⌊2 * x⌋₊ < 2 * ⌊x⌋₊ + 2 := by
      have := Nat.lt_floor_add_one x
      have h2 : 2 * x < 2 * (⌊x⌋₊ + 1) := by linarith
      have h3 : (⌊2 * x⌋₊ : ℝ) ≤ 2 * x := Nat.floor_le (mul_nonneg (by norm_num) hx)
      have h4 : (⌊2 * x⌋₊ : ℝ) < 2 * ⌊x⌋₊ + 2 := by linarith
      exact_mod_cast h4
    have hy_lt : ⌊2 * y⌋₊ < 2 * ⌊y⌋₊ + 2 := by
      have := Nat.lt_floor_add_one y
      have h2 : 2 * y < 2 * (⌊y⌋₊ + 1) := by linarith
      have h3 : (⌊2 * y⌋₊ : ℝ) ≤ 2 * y := Nat.floor_le (mul_nonneg (by norm_num) hy)
      have h4 : (⌊2 * y⌋₊ : ℝ) < 2 * ⌊y⌋₊ + 2 := by linarith
      exact_mod_cast h4
    omega
  · have hxeven : ⌊2 * x⌋₊ % 2 = 0 := Nat.mod_two_eq_zero_or_one (⌊2 * x⌋₊) |>.resolve_right hxodd
    have hyeven := h_mod ▸ hxeven
    have hx_le := floor_two_mul_even_le hx hxeven
    have hy_le := floor_two_mul_even_le hy hyeven
    have hx_ge : ⌊2 * x⌋₊ ≥ 2 * ⌊x⌋₊ := by
      have h1 : (2 * ⌊x⌋₊ : ℕ) ≤ ⌊2 * x⌋₊ := by
        have hfloor := Nat.floor_le hx
        apply Nat.le_floor
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        linarith
      exact h1
    have hy_ge : ⌊2 * y⌋₊ ≥ 2 * ⌊y⌋₊ := by
      have h1 : (2 * ⌊y⌋₊ : ℕ) ≤ ⌊2 * y⌋₊ := by
        have hfloor := Nat.floor_le hy
        apply Nat.le_floor
        simp only [Nat.cast_mul, Nat.cast_ofNat]
        linarith
      exact h1
    omega

