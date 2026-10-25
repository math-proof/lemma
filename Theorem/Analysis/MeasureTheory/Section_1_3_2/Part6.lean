import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Def.Analysis.MeasureTheory.Section_1_3_2.Part6
set_option doc.verso.suggestions false


namespace Remark_1_3_10

/-- The series ∑ 2·bⱼ(x)·3^(-j) is summable for any x. -/
lemma binaryToTernary_summable (x : ℝ) :
    Summable (fun j => (2 * binaryDigit x (j + 1) : ℝ) * (1/3:ℝ)^(j + 1)) := by
  apply Summable.of_nonneg_of_le
  · intro j
    apply mul_nonneg
    · exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    · positivity
  · intro j
    have h1 : (binaryDigit x (j + 1) : ℝ) ≤ 1 := by exact_mod_cast binaryDigit_le_one x (j + 1)
    calc (2 * binaryDigit x (j + 1) : ℝ) * (1/3:ℝ)^(j + 1)
        ≤ (2 * 1) * (1/3:ℝ)^(j + 1) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/3) (j + 1)]
      _ = 2 * (1/3:ℝ)^(j + 1) := by ring
  · have h : Summable (fun j : ℕ => (1/3:ℝ)^j) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
    exact (h.mul_left 2).comp_injective (fun _ _ h => Nat.succ_injective h)

/-! # Helper lemmas for monotonicity proof -/

/-- For x ∈ (0, 1), there exists a position where the binary digit is 1. -/
lemma binaryDigit_exists_one_of_pos {x : ℝ} (hx_pos : 0 < x) (hx_lt : x < 1) :
    ∃ j, binaryDigit x (j + 1) = 1 := by
  have hx_Ico : x ∈ Set.Ico (0:ℝ) 1 := ⟨le_of_lt hx_pos, hx_lt⟩
  have hinv_ge_one : 1 ≤ x⁻¹ := Bound.one_le_inv₀ hx_pos (le_of_lt hx_lt)
  have h_pow_exists := exists_nat_pow_near hinv_ge_one (by norm_num : (1:ℝ) < 2)
  obtain ⟨n, hn_le, hn_lt⟩ := h_pow_exists
  have h_pow_unbounded : ∃ j : ℕ, 1 ≤ (2:ℝ)^(j+1) * x := by
    use n
    have h2n_pos : (0:ℝ) < 2^n := by positivity
    calc (1:ℝ) = x⁻¹ * x := (inv_mul_cancel₀ (ne_of_gt hx_pos)).symm
      _ ≤ (2:ℝ)^(n+1) * x := by nlinarith
  let j := Nat.find h_pow_unbounded
  have hj_ge : 1 ≤ (2:ℝ)^(j+1) * x := Nat.find_spec h_pow_unbounded
  have hj_lt : (2:ℝ)^(j+1) * x < 2 := by
    by_cases hj0 : j = 0
    · simp only [hj0, zero_add, pow_one]
      calc 2 * x < 2 * 1 := by nlinarith [hx_Ico.2]
        _ = 2 := by ring
    · have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
      have hj_pred : j - 1 < j := Nat.sub_lt hj_pos Nat.one_pos
      have := Nat.find_min h_pow_unbounded hj_pred
      simp only [not_le] at this
      have hj_sub : j - 1 + 1 = j := Nat.sub_add_cancel hj_pos
      rw [hj_sub] at this
      calc (2:ℝ)^(j+1) * x = 2 * ((2:ℝ)^j * x) := by rw [pow_succ]; ring
        _ < 2 * 1 := by nlinarith
        _ = 2 := by ring
  have h_floor_eq : ⌊(2:ℝ)^(j+1) * x⌋₊ = 1 := by
    apply Nat.floor_eq_on_Ico 1
    constructor
    · simp only [Nat.cast_one]; exact hj_ge
    · simp only [Nat.cast_one]; linarith
  exact ⟨j, by simp only [binaryDigit, if_pos hx_Ico, h_floor_eq]⟩

/-- The partial sum bounds x from below: Sₙ(x) ≤ x -/
lemma binaryDigit_partial_sum_le {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) (n : ℕ) :
    (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n ≤ x := by
  have h2n_pos : (0:ℝ) < 2^n := by positivity
  rw [div_le_iff₀ h2n_pos, mul_comm]
  exact Nat.floor_le (mul_nonneg hx.1 (le_of_lt h2n_pos))

/-- The partial sum bounds x from above: x < Sₙ(x) + 2^(-n) -/
lemma binaryDigit_partial_sum_lt (x : ℝ) (n : ℕ) :
    x < (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n + (1:ℝ) / (2:ℝ)^n := by
  have h2n_pos : (0:ℝ) < 2^n := by positivity
  have := Nat.lt_floor_add_one ((2:ℝ)^n * x)
  have h1 : (2:ℝ)^n * x < ⌊(2:ℝ)^n * x⌋₊ + 1 := this
  calc x = ((2:ℝ)^n * x) / (2:ℝ)^n := by field_simp
    _ < (⌊(2:ℝ)^n * x⌋₊ + 1 : ℝ) / (2:ℝ)^n := by
        apply div_lt_div_of_pos_right h1 h2n_pos
    _ = (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n + (1:ℝ) / (2:ℝ)^n := by ring

/-- Key lemma: if bₖ(x) = 1, then `x ≥ floor(2^k * x) / 2^k + 2^(-(k+1))` -/
lemma binaryDigit_one_implies_lower_bound {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) (k : ℕ)
    (hbk : binaryDigit x (k + 1) = 1) :
    (⌊(2:ℝ)^k * x⌋₊ : ℝ) / (2:ℝ)^k + (1:ℝ) / (2:ℝ)^(k + 1) ≤ x := by
  simp only [binaryDigit, if_pos hx] at hbk
  have heq : (2:ℝ)^(k+1) * x = 2 * ((2:ℝ)^k * x) := by ring
  have h_floor_odd : ⌊2 * ((2:ℝ)^k * x)⌋₊ % 2 = 1 := by rw [← heq]; exact hbk
  have h2k1_pos : (0:ℝ) < 2^(k+1) := by positivity
  have h2k1_nonneg : (0:ℝ) ≤ 2^(k+1) := le_of_lt h2k1_pos
  have hx_nonneg : 0 ≤ (2:ℝ)^k * x := mul_nonneg (by positivity) hx.1
  have h_floor_rel : ⌊(2:ℝ)^(k+1) * x⌋₊ ≥ 2 * ⌊(2:ℝ)^k * x⌋₊ + 1 := by
    rw [heq]
    exact floor_two_mul_odd_ge hx_nonneg h_floor_odd
  calc (⌊(2:ℝ)^k * x⌋₊ : ℝ) / (2:ℝ)^k + (1:ℝ) / (2:ℝ)^(k + 1)
      = (2 * ⌊(2:ℝ)^k * x⌋₊ + 1) / (2:ℝ)^(k + 1) := by field_simp; ring
    _ ≤ (⌊(2:ℝ)^(k+1) * x⌋₊ : ℝ) / (2:ℝ)^(k + 1) := by
        apply div_le_div_of_nonneg_right _ h2k1_nonneg
        exact_mod_cast h_floor_rel
    _ ≤ x := binaryDigit_partial_sum_le hx (k + 1)

/-- Key lemma: if bₖ(y) = 0, then `y < floor(2^k * y) / 2^k + 2^(-(k+1))` -/
lemma binaryDigit_zero_implies_upper_bound {y : ℝ} (hy : y ∈ Set.Ico (0:ℝ) 1) (k : ℕ)
    (hbk : binaryDigit y (k + 1) = 0) :
    y < (⌊(2:ℝ)^k * y⌋₊ : ℝ) / (2:ℝ)^k + (1:ℝ) / (2:ℝ)^(k + 1) := by
  simp only [binaryDigit, if_pos hy] at hbk
  have heq : (2:ℝ)^(k+1) * y = 2 * ((2:ℝ)^k * y) := by ring
  have h_floor_even : ⌊2 * ((2:ℝ)^k * y)⌋₊ % 2 = 0 := by rw [← heq]; exact hbk
  have h2k1_pos : (0:ℝ) < 2^(k+1) := by positivity
  have h2k1_nonneg : (0:ℝ) ≤ 2^(k+1) := le_of_lt h2k1_pos
  have hy_nonneg : 0 ≤ (2:ℝ)^k * y := mul_nonneg (by positivity) hy.1
  have h_floor_rel : ⌊(2:ℝ)^(k+1) * y⌋₊ ≤ 2 * ⌊(2:ℝ)^k * y⌋₊ := by
    rw [heq]
    exact floor_two_mul_even_le hy_nonneg h_floor_even
  have h_lt := binaryDigit_partial_sum_lt y (k + 1)
  calc y < (⌊(2:ℝ)^(k+1) * y⌋₊ : ℝ) / (2:ℝ)^(k + 1) + (1:ℝ) / (2:ℝ)^(k + 1) := h_lt
    _ = (⌊(2:ℝ)^(k+1) * y⌋₊ + 1 : ℝ) / (2:ℝ)^(k + 1) := by ring
    _ ≤ (2 * ⌊(2:ℝ)^k * y⌋₊ + 1 : ℝ) / (2:ℝ)^(k + 1) := by
        apply div_le_div_of_nonneg_right _ h2k1_nonneg
        have : (⌊(2:ℝ)^(k+1) * y⌋₊ : ℝ) + 1 ≤ 2 * ⌊(2:ℝ)^k * y⌋₊ + 1 := by
          exact_mod_cast Nat.add_le_add_right h_floor_rel 1
        linarith
    _ = (⌊(2:ℝ)^k * y⌋₊ : ℝ) / (2:ℝ)^k + (1:ℝ) / (2:ℝ)^(k + 1) := by field_simp; ring

/-- Helper: floors of x, y in \[0,1) are equal up to level n if their binary digits agree up to level n-1. -/
lemma floor_eq_of_binaryDigit_eq {x y : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) (hy : y ∈ Set.Ico (0:ℝ) 1)
    (heq : ∀ j < n, binaryDigit x (j + 1) = binaryDigit y (j + 1)) :
    ⌊(2:ℝ)^n * x⌋₊ = ⌊(2:ℝ)^n * y⌋₊ := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    have hx01 : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith [hx.2] : x < 1)
    have hy01 : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith [hy.2] : y < 1)
    simp [hx01, hy01]
  | succ n ih =>
    have h_prev : ∀ j < n, binaryDigit x (j + 1) = binaryDigit y (j + 1) := fun j hj => heq j (Nat.lt_succ_of_lt hj)
    have ih' := ih h_prev
    simp only [binaryDigit, if_pos hx, if_pos hy] at heq
    have hmod_eq := heq n (Nat.lt_succ_self n)
    have hx_nonneg : 0 ≤ (2:ℝ)^n * x := mul_nonneg (by positivity) hx.1
    have hy_nonneg : 0 ≤ (2:ℝ)^n * y := mul_nonneg (by positivity) hy.1
    have h1 : (2:ℝ)^(n+1) * x = 2 * ((2:ℝ)^n * x) := by ring
    have h2 : (2:ℝ)^(n+1) * y = 2 * ((2:ℝ)^n * y) := by ring
    have hmod_eq' : ⌊2 * ((2:ℝ)^n * x)⌋₊ % 2 = ⌊2 * ((2:ℝ)^n * y)⌋₊ % 2 := by
      rw [← h1, ← h2]; exact hmod_eq
    rw [h1, h2]
    exact floor_two_mul_eq_of_mod_eq hx_nonneg hy_nonneg ih' hmod_eq'

/-- For x, y ∈ \[0,1) with x < y, there exists a first position k where bₖ(x) < bₖ(y). -/
lemma binaryDigit_first_diff {x y : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) (hy : y ∈ Set.Ico (0:ℝ) 1)
    (hxy : x < y) :
    ∃ k, binaryDigit x (k + 1) < binaryDigit y (k + 1) ∧
         ∀ j < k, binaryDigit x (j + 1) = binaryDigit y (j + 1) := by
  have h_exists_diff : ∃ j, binaryDigit x (j + 1) ≠ binaryDigit y (j + 1) := by
    by_contra h_all_eq
    push_neg at h_all_eq
    have h_floor_eq : ∀ n, ⌊(2:ℝ)^n * x⌋₊ = ⌊(2:ℝ)^n * y⌋₊ := by
      intro n
      exact floor_eq_of_binaryDigit_eq hx hy (fun j _ => h_all_eq j)
    have h_close : ∀ n, |x - y| < (1:ℝ) / (2:ℝ)^n := by
      intro n
      have hx_bounds := binaryDigit_partial_sum_le hx n
      have hx_bounds' := binaryDigit_partial_sum_lt x n
      have hy_bounds := binaryDigit_partial_sum_le hy n
      have hy_bounds' := binaryDigit_partial_sum_lt y n
      rw [h_floor_eq n] at hx_bounds hx_bounds'
      rw [abs_lt]
      constructor <;> linarith
    have hxy_eq : x = y := by
      by_contra hne
      have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1:ℝ)/2 < 1)
      have := h_close n
      have h1 : (1:ℝ) / 2^n = (1/2)^n := by simp [div_eq_mul_inv]
      linarith
    exact absurd hxy_eq (ne_of_lt hxy)
  let k := Nat.find h_exists_diff
  have hk_diff : binaryDigit x (k + 1) ≠ binaryDigit y (k + 1) := Nat.find_spec h_exists_diff
  have hk_first : ∀ j < k, binaryDigit x (j + 1) = binaryDigit y (j + 1) := by
    intro j hj
    exact of_not_not (Nat.find_min h_exists_diff hj)
  have hbx := binaryDigit_le_one x (k + 1)
  have hby := binaryDigit_le_one y (k + 1)
  by_cases h : binaryDigit x (k + 1) < binaryDigit y (k + 1)
  · exact ⟨k, h, hk_first⟩
  · push_neg at h
    have hbx_eq : binaryDigit x (k + 1) = 1 := by omega
    have hby_eq : binaryDigit y (k + 1) = 0 := by omega
    exfalso
    have hx_lb := binaryDigit_one_implies_lower_bound hx k hbx_eq
    have hy_ub := binaryDigit_zero_implies_upper_bound hy k hby_eq
    have h_floor_eq : ⌊(2:ℝ)^k * x⌋₊ = ⌊(2:ℝ)^k * y⌋₊ := floor_eq_of_binaryDigit_eq hx hy hk_first
    rw [h_floor_eq] at hx_lb
    linarith

/-- Monotonicity: if digits agree up to k and bₖ(x) < bₖ(y), then g(x) < g(y). -/
lemma binaryToTernary_lt_of_digit_lt {x y : ℝ}
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1) (k : ℕ)
    (hk_lt : binaryDigit x (k + 1) < binaryDigit y (k + 1))
    (hk_eq : ∀ j < k, binaryDigit x (j + 1) = binaryDigit y (j + 1)) :
    binaryToTernaryFn x < binaryToTernaryFn y := by
  have hbx_le := binaryDigit_le_one x (k + 1)
  have hby_le := binaryDigit_le_one y (k + 1)
  have hbx_zero : binaryDigit x (k + 1) = 0 := by omega
  have hby_one : binaryDigit y (k + 1) = 1 := by omega
  simp only [binaryToTernaryFn, if_pos hx, if_pos hy]
  let fx := fun j => (2 * binaryDigit x (j + 1) : ℝ) * (1/3:ℝ)^(j + 1)
  let fy := fun j => (2 * binaryDigit y (j + 1) : ℝ) * (1/3:ℝ)^(j + 1)
  have h_first_eq : ∑ j ∈ Finset.range k, fx j = ∑ j ∈ Finset.range k, fy j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [fx, fy]
    rw [hk_eq j (Finset.mem_range.mp hj)]
  have h_term_x : fx k = 0 := by simp only [fx, hbx_zero, Nat.cast_zero, mul_zero, zero_mul]
  have h_term_y : fy k = (2:ℝ) * (1/3:ℝ)^(k + 1) := by
    simp only [fy, hby_one, Nat.cast_one, mul_one]
  have h_tail_x : ∑' j, fx (k + 1 + j) ≤ (1/3:ℝ)^(k + 1) := by
    calc ∑' j, fx (k + 1 + j)
        = ∑' j, (2 * binaryDigit x (k + 1 + j + 1) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := rfl
      _ ≤ ∑' j, (2:ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
          apply Summable.tsum_le_tsum
          · intro j
            have hb := binaryDigit_le_one x (k + 1 + j + 1)
            have hb_real : (binaryDigit x (k + 1 + j + 1) : ℝ) ≤ 1 := by exact_mod_cast hb
            have h3pos : (0:ℝ) < (1/3)^(k + 1 + j + 1) := by positivity
            calc (2 * binaryDigit x (k + 1 + j + 1) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1)
                = 2 * (binaryDigit x (k + 1 + j + 1) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by ring
              _ ≤ 2 * 1 * (1/3:ℝ)^(k + 1 + j + 1) := by nlinarith
              _ = 2 * (1/3:ℝ)^(k + 1 + j + 1) := by ring
          · exact (binaryToTernary_summable x).comp_injective (fun j₁ j₂ h => by omega)
          · have h : Summable (fun j : ℕ => (1/3:ℝ)^j) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
            exact (h.mul_left 2).comp_injective (fun j₁ j₂ h => by omega)
      _ = (1/3:ℝ)^(k + 1) := by
          have h1 := tsum_geometric_of_lt_one (r := (1/3:ℝ)) (by norm_num) (by norm_num)
          calc ∑' j, (2:ℝ) * (1/3:ℝ)^(k + 1 + j + 1)
              = ∑' j, (2:ℝ) * ((1/3:ℝ)^(k + 2) * (1/3:ℝ)^j) := by
                congr 1; ext j; rw [← pow_add]; ring_nf
            _ = (2:ℝ) * (1/3:ℝ)^(k + 2) * ∑' j, (1/3:ℝ)^j := by
                rw [← tsum_mul_left]; congr 1; ext j; ring
            _ = (2:ℝ) * (1/3:ℝ)^(k + 2) * (1 - 1/3)⁻¹ := by rw [h1]
            _ = (1/3:ℝ)^(k + 1) := by field_simp; ring
  have h_tail_y_nonneg : 0 ≤ ∑' j, fy (k + 1 + j) := by
    apply tsum_nonneg; intro j; simp only [fy]; positivity
  have hsum_x : Summable fx := binaryToTernary_summable x
  have hsum_y : Summable fy := binaryToTernary_summable y
  have h_split_x : ∑' j, fx j = ∑ j ∈ Finset.range k, fx j + fx k + ∑' j, fx (k + 1 + j) := by
    rw [← Summable.sum_add_tsum_nat_add (k + 1) hsum_x, Finset.sum_range_succ]
    congr 1
    congr 1
    ext j
    congr 1
    omega
  have h_split_y : ∑' j, fy j = ∑ j ∈ Finset.range k, fy j + fy k + ∑' j, fy (k + 1 + j) := by
    rw [← Summable.sum_add_tsum_nat_add (k + 1) hsum_y, Finset.sum_range_succ]
    congr 1
    congr 1
    ext j
    congr 1
    omega
  rw [h_split_x, h_split_y, h_first_eq, h_term_x, h_term_y]
  have h3pos : (0:ℝ) < (1/3)^(k + 1) := by positivity
  linarith

/-! # Helper lemmas for injectivity proof -/

/-- Ternary \{0,2\} expansions are unique. -/
lemma ternary_02_expansion_unique {d e : ℕ → ℕ}
    (hd : ∀ j, d j ∈ ({0, 2} : Set ℕ))
    (he : ∀ j, e j ∈ ({0, 2} : Set ℕ))
    (hsum_d : Summable (fun j => (d j : ℝ) * (1/3:ℝ)^(j + 1)))
    (hsum_e : Summable (fun j => (e j : ℝ) * (1/3:ℝ)^(j + 1)))
    (heq : ∑' j, (d j : ℝ) * (1/3:ℝ)^(j + 1) = ∑' j, (e j : ℝ) * (1/3:ℝ)^(j + 1)) :
    ∀ j, d j = e j := by
  by_contra h_ne
  push_neg at h_ne
  have h_exists : ∃ k, d k ≠ e k := h_ne
  let k := Nat.find h_exists
  have hk_ne : d k ≠ e k := Nat.find_spec h_exists
  have hk_eq : ∀ j < k, d j = e j := fun j hj => by
    by_contra h
    exact Nat.find_min h_exists hj h
  have hd_k := hd k
  have he_k := he k
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd_k he_k
  rcases hd_k with hdk0 | hdk2 <;> rcases he_k with hek0 | hek2
  · omega
  ·
    have h_first_eq : ∑ j ∈ Finset.range k, (d j : ℝ) * (1/3:ℝ)^(j + 1) =
        ∑ j ∈ Finset.range k, (e j : ℝ) * (1/3:ℝ)^(j + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hk_eq j (Finset.mem_range.mp hj)]
    have h_split_d : ∑' j, (d j : ℝ) * (1/3:ℝ)^(j + 1) =
        ∑ j ∈ Finset.range k, (d j : ℝ) * (1/3:ℝ)^(j + 1) + (d k : ℝ) * (1/3:ℝ)^(k + 1) +
        ∑' j, (d (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
      rw [← Summable.sum_add_tsum_nat_add (k + 1) hsum_d, Finset.sum_range_succ]
      congr 1; congr 1
      funext j; simp only [add_comm j (k + 1)]
    have h_split_e : ∑' j, (e j : ℝ) * (1/3:ℝ)^(j + 1) =
        ∑ j ∈ Finset.range k, (e j : ℝ) * (1/3:ℝ)^(j + 1) + (e k : ℝ) * (1/3:ℝ)^(k + 1) +
        ∑' j, (e (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
      rw [← Summable.sum_add_tsum_nat_add (k + 1) hsum_e, Finset.sum_range_succ]
      congr 1; congr 1
      funext j; simp only [add_comm j (k + 1)]
    rw [h_split_d, h_split_e, h_first_eq, hdk0, hek2] at heq
    simp only [Nat.cast_zero, zero_mul, Nat.cast_ofNat] at heq
    have h_tail_d_bound : ∑' j, (d (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) ≤ (1/3:ℝ)^(k + 1) := by
      calc ∑' j, (d (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1)
          ≤ ∑' j, (2:ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
            apply Summable.tsum_le_tsum
            · intro j
              have hdj := hd (k + 1 + j)
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdj
              rcases hdj with hdj0 | hdj2
              · simp only [hdj0, Nat.cast_zero, zero_mul]; positivity
              · simp only [hdj2, Nat.cast_ofNat]; exact le_rfl
            · exact hsum_d.comp_injective (fun _ _ h => by omega)
            · have h : Summable (fun j : ℕ => (1/3:ℝ)^j) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
              exact (h.mul_left 2).comp_injective (fun _ _ h => by omega)
        _ = (1/3:ℝ)^(k + 1) := by
            have h1 := tsum_geometric_of_lt_one (r := (1/3:ℝ)) (by norm_num) (by norm_num)
            calc ∑' j, (2:ℝ) * (1/3:ℝ)^(k + 1 + j + 1)
                = ∑' j, (2:ℝ) * ((1/3:ℝ)^(k + 2) * (1/3:ℝ)^j) := by
                  congr 1; ext j; rw [← pow_add]; ring_nf
              _ = (2:ℝ) * (1/3:ℝ)^(k + 2) * ∑' j, (1/3:ℝ)^j := by
                  rw [← tsum_mul_left]; congr 1; ext j; ring
              _ = (2:ℝ) * (1/3:ℝ)^(k + 2) * (1 - 1/3)⁻¹ := by rw [h1]
              _ = (1/3:ℝ)^(k + 1) := by field_simp; ring
    have h_tail_e_nonneg : 0 ≤ ∑' j, (e (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
      apply tsum_nonneg; intro j; positivity
    have h3pos : (0:ℝ) < (1/3)^(k + 1) := by positivity
    linarith
  ·
    have h_first_eq : ∑ j ∈ Finset.range k, (d j : ℝ) * (1/3:ℝ)^(j + 1) =
        ∑ j ∈ Finset.range k, (e j : ℝ) * (1/3:ℝ)^(j + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hk_eq j (Finset.mem_range.mp hj)]
    have h_split_d : ∑' j, (d j : ℝ) * (1/3:ℝ)^(j + 1) =
        ∑ j ∈ Finset.range k, (d j : ℝ) * (1/3:ℝ)^(j + 1) + (d k : ℝ) * (1/3:ℝ)^(k + 1) +
        ∑' j, (d (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
      rw [← Summable.sum_add_tsum_nat_add (k + 1) hsum_d, Finset.sum_range_succ]
      congr 1; congr 1
      funext j; simp only [add_comm j (k + 1)]
    have h_split_e : ∑' j, (e j : ℝ) * (1/3:ℝ)^(j + 1) =
        ∑ j ∈ Finset.range k, (e j : ℝ) * (1/3:ℝ)^(j + 1) + (e k : ℝ) * (1/3:ℝ)^(k + 1) +
        ∑' j, (e (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
      rw [← Summable.sum_add_tsum_nat_add (k + 1) hsum_e, Finset.sum_range_succ]
      congr 1; congr 1
      funext j; simp only [add_comm j (k + 1)]
    rw [h_split_d, h_split_e, h_first_eq, hdk2, hek0] at heq
    simp only [Nat.cast_zero, zero_mul, Nat.cast_ofNat] at heq
    have h_tail_e_bound : ∑' j, (e (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) ≤ (1/3:ℝ)^(k + 1) := by
      calc ∑' j, (e (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1)
          ≤ ∑' j, (2:ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
            apply Summable.tsum_le_tsum
            · intro j
              have hej := he (k + 1 + j)
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hej
              rcases hej with hej0 | hej2
              · simp only [hej0, Nat.cast_zero, zero_mul]; positivity
              · simp only [hej2, Nat.cast_ofNat]; exact le_rfl
            · exact hsum_e.comp_injective (fun _ _ h => by omega)
            · have h : Summable (fun j : ℕ => (1/3:ℝ)^j) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
              exact (h.mul_left 2).comp_injective (fun _ _ h => by omega)
        _ = (1/3:ℝ)^(k + 1) := by
            have h1 := tsum_geometric_of_lt_one (r := (1/3:ℝ)) (by norm_num) (by norm_num)
            calc ∑' j, (2:ℝ) * (1/3:ℝ)^(k + 1 + j + 1)
                = ∑' j, (2:ℝ) * ((1/3:ℝ)^(k + 2) * (1/3:ℝ)^j) := by
                  congr 1; ext j; rw [← pow_add]; ring_nf
              _ = (2:ℝ) * (1/3:ℝ)^(k + 2) * ∑' j, (1/3:ℝ)^j := by
                  rw [← tsum_mul_left]; congr 1; ext j; ring
              _ = (2:ℝ) * (1/3:ℝ)^(k + 2) * (1 - 1/3)⁻¹ := by rw [h1]
              _ = (1/3:ℝ)^(k + 1) := by field_simp; ring
    have h_tail_d_nonneg : 0 ≤ ∑' j, (d (k + 1 + j) : ℝ) * (1/3:ℝ)^(k + 1 + j + 1) := by
      apply tsum_nonneg; intro j; positivity
    have h3pos : (0:ℝ) < (1/3)^(k + 1) := by positivity
    linarith
  · omega

/-! # Helper lemmas for binary expansion sums -/

/-- ⌊2y⌋ = 2⌊y⌋ + ⌊2y⌋ % 2 for y ≥ 0. -/
private lemma floor_two_mul_decomp {y : ℝ} (_hy : 0 ≤ y) :
    ⌊2 * y⌋₊ = 2 * ⌊y⌋₊ + ⌊2 * y⌋₊ % 2 := by
  have h := Nat.div_add_mod ⌊2 * y⌋₊ 2
  have h_div : ⌊2 * y⌋₊ / 2 = ⌊y⌋₊ := Nat.cast_mul_floor_div_cancel (by norm_num : (2:ℕ) ≠ 0) y
  omega

/-- Partial sum identity: `∑ (j < n) bⱼ * 2^(-(j+1)) = floor(2^n * x) / 2^n`. -/
private lemma partial_sum_eq_floor {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1) =
    (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero]
    have h0 : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hx.2
    simp [h0]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h2n_pos : (0:ℝ) < 2^n := by positivity
    have hx_nonneg : 0 ≤ x := hx.1
    have hb : binaryDigit x (n + 1) = ⌊(2:ℝ)^(n+1) * x⌋₊ % 2 := by
      simp only [binaryDigit, if_pos hx]
    have h_floor : ⌊(2:ℝ)^(n+1) * x⌋₊ = 2 * ⌊(2:ℝ)^n * x⌋₊ + ⌊(2:ℝ)^(n+1) * x⌋₊ % 2 := by
      have h2 : (2:ℝ)^(n+1) * x = 2 * ((2:ℝ)^n * x) := by ring
      rw [h2]
      exact floor_two_mul_decomp (mul_nonneg (le_of_lt h2n_pos) hx_nonneg)
    rw [hb]
    have h2n_ne : (2:ℝ)^n ≠ 0 := ne_of_gt h2n_pos
    have h_pow_succ : (2:ℝ)^(n+1) = 2 * 2^n := by ring
    rw [h_pow_succ]
    have h_half_pow : (1/2:ℝ)^(n+1) = 1 / (2 * 2^n) := by
      rw [← h_pow_succ]; simp [div_eq_mul_inv]
    rw [h_half_pow]
    have h_floor' : (⌊2 * 2^n * x⌋₊ : ℝ) = 2 * (⌊(2:ℝ)^n * x⌋₊ : ℝ) + (⌊2 * 2^n * x⌋₊ % 2 : ℕ) := by
      have h2eq : (2:ℝ) * 2^n * x = (2:ℝ)^(n+1) * x := by ring
      rw [h2eq]
      exact_mod_cast h_floor
    have h2_2n_pos : (0:ℝ) < 2 * 2^n := by positivity
    have h2_2n_ne : (2:ℝ) * 2^n ≠ 0 := ne_of_gt h2_2n_pos
    rw [h_floor']
    field_simp

/-- Binary series is summable for x ∈ \[0,1). -/
private lemma binary_summable {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) :
    Summable (fun j => (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1)) := by
  apply Summable.of_nonneg_of_le
  · intro j; positivity
  · intro j
    have h1 : (binaryDigit x (j + 1) : ℝ) ≤ 1 := by
      have : binaryDigit x (j + 1) ≤ 1 := by
        simp only [binaryDigit, if_pos hx]
        omega
      exact_mod_cast this
    calc (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1)
        ≤ 1 * (1/2:ℝ)^(j + 1) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) (j + 1)]
      _ = (1/2:ℝ)^(j + 1) := by ring
  · have h : Summable (fun j : ℕ => (1/2:ℝ)^j) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
    exact h.comp_injective (fun _ _ h => Nat.succ_injective h)

/-- For non-dyadic x ∈ \[0,1), x equals its binary expansion sum. -/
lemma non_dyadic_eq_binary_sum {x : ℝ} (hx : x ∈ Set.Ico (0:ℝ) 1) (_hnd : x ∉ DyadicRationals) :
    x = ∑' j : ℕ, (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1) := by
  have h_summable := binary_summable hx
  have h_partial_to_tsum : Filter.Tendsto
      (fun n => ∑ j ∈ Finset.range n, (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1))
      Filter.atTop (nhds (∑' j, (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1))) :=
    h_summable.hasSum.tendsto_sum_nat
  have h_partial_eq : ∀ n, ∑ j ∈ Finset.range n, (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1) =
      (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n := partial_sum_eq_floor hx
  have h_floor_to_x : Filter.Tendsto (fun n => (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n) Filter.atTop (nhds x) := by
    have h_lower : ∀ n, (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n ≤ x := fun n => by
      have h2n_pos : (0:ℝ) < 2^n := by positivity
      rw [div_le_iff₀ h2n_pos, mul_comm]
      exact Nat.floor_le (mul_nonneg hx.1 (le_of_lt h2n_pos))
    have h_upper : ∀ n, x < (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n + (1:ℝ) / (2:ℝ)^n := fun n => by
      have h2n_pos : (0:ℝ) < 2^n := by positivity
      have := Nat.lt_floor_add_one ((2:ℝ)^n * x)
      calc x = ((2:ℝ)^n * x) / (2:ℝ)^n := by field_simp
        _ < (⌊(2:ℝ)^n * x⌋₊ + 1 : ℝ) / (2:ℝ)^n := by apply div_lt_div_of_pos_right this h2n_pos
        _ = (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n + (1:ℝ) / (2:ℝ)^n := by ring
    have h_gap : Filter.Tendsto (fun n : ℕ => (1:ℝ) / (2:ℝ)^n) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ((1:ℝ)/2)^n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      convert h1 using 1; ext n; simp [div_eq_mul_inv]
    have h_between : ∀ n, x - (1:ℝ) / (2:ℝ)^n < (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n ∧
        (⌊(2:ℝ)^n * x⌋₊ : ℝ) / (2:ℝ)^n ≤ x := fun n => ⟨by linarith [h_upper n], h_lower n⟩
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    rw [Metric.tendsto_atTop] at h_gap
    obtain ⟨N, hN⟩ := h_gap ε hε
    use N
    intro n hn
    specialize hN n hn
    simp only [Real.dist_eq, sub_zero] at hN
    rw [abs_of_pos (by positivity)] at hN
    have hbn := h_between n
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hbn.1, hbn.2]
  have h_partial_to_x : Filter.Tendsto
      (fun n => ∑ j ∈ Finset.range n, (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1))
      Filter.atTop (nhds x) := by
    simp_rw [h_partial_eq]
    exact h_floor_to_x
  exact tendsto_nhds_unique h_partial_to_x h_partial_to_tsum

/-- Non-dyadic x ∈ \[0,1) with equal binary digits are equal. -/
lemma eq_of_binaryDigit_eq_of_non_dyadic {x₁ x₂ : ℝ}
    (hx₁ : x₁ ∈ Set.Ico (0:ℝ) 1) (hx₂ : x₂ ∈ Set.Ico (0:ℝ) 1)
    (hnd₁ : x₁ ∉ DyadicRationals) (hnd₂ : x₂ ∉ DyadicRationals)
    (heq : ∀ j, binaryDigit x₁ j = binaryDigit x₂ j) :
    x₁ = x₂ := by
  have h1 := non_dyadic_eq_binary_sum hx₁ hnd₁
  have h2 := non_dyadic_eq_binary_sum hx₂ hnd₂
  rw [h1, h2]
  congr 1
  ext j
  rw [heq (j + 1)]

/-! # Helper lemmas for image_in_cantor -/

/-- Points with \{0,2\} ternary digits are in the Cantor set. -/
lemma mem_CantorSet_of_ternary_02 {y : ℝ} (d : ℕ → ℕ)
    (hd : ∀ j, d j ∈ ({0, 2} : Set ℕ))
    (hsum : Summable (fun j => (d j : ℝ) * (1/3:ℝ)^(j + 1)))
    (hy : y = ∑' j, (d j : ℝ) * (1/3:ℝ)^(j + 1)) :
    y ∈ CantorSet ∨ y = 0 := by
  left
  rw [CantorSet]
  simp only [Set.mem_iInter]
  intro n
  let a : Fin n → ({0, 2} : Set ℕ) := fun i => ⟨d i.val, hd i.val⟩
  rw [CantorInterval]
  simp only [Set.mem_iUnion]
  use a
  simp only [BoundedInterval.set_Icc, Set.mem_Icc]
  have h_split : y = ∑ j ∈ Finset.range n, (d j : ℝ) * (1/3:ℝ)^(j + 1) +
      ∑' j, (d (n + j) : ℝ) * (1/3:ℝ)^(n + j + 1) := by
    rw [hy, ← Summable.sum_add_tsum_nat_add n hsum]
    congr 1
    apply tsum_congr
    intro j
    rw [add_comm j n]
  have h_partial : ∑ j ∈ Finset.range n, (d j : ℝ) * (1/3:ℝ)^(j + 1) =
      ∑ i : Fin n, (a i : ℝ) / (3:ℝ)^(i.val + 1) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [dif_pos hj]
    simp only [a]
    field_simp; ring_nf; simp
  have h_tail_nonneg : 0 ≤ ∑' j, (d (n + j) : ℝ) * (1/3:ℝ)^(n + j + 1) := by
    apply tsum_nonneg; intro j; positivity
  have h_tail_bound : ∑' j, (d (n + j) : ℝ) * (1/3:ℝ)^(n + j + 1) ≤ (1/3:ℝ)^n := by
    calc ∑' j, (d (n + j) : ℝ) * (1/3:ℝ)^(n + j + 1)
        ≤ ∑' j, (2:ℝ) * (1/3:ℝ)^(n + j + 1) := by
          apply Summable.tsum_le_tsum
          · intro j
            have hdj := hd (n + j)
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdj
            rcases hdj with hdj0 | hdj2
            · simp only [hdj0, Nat.cast_zero, zero_mul]; positivity
            · simp only [hdj2, Nat.cast_ofNat]; exact le_refl _
          · exact hsum.comp_injective (fun _ _ h => by omega)
          · have h : Summable (fun j : ℕ => (1/3:ℝ)^j) :=
              summable_geometric_of_lt_one (by norm_num) (by norm_num)
            exact (h.mul_left 2).comp_injective (fun _ _ h => by omega)
      _ = (1/3:ℝ)^n := by
          have h1 := tsum_geometric_of_lt_one (r := (1/3:ℝ)) (by norm_num) (by norm_num)
          calc ∑' j, (2:ℝ) * (1/3:ℝ)^(n + j + 1)
              = ∑' j, (2:ℝ) * ((1/3:ℝ)^(n + 1) * (1/3:ℝ)^j) := by
                congr 1; ext j; rw [← pow_add]; ring_nf
            _ = (2:ℝ) * (1/3:ℝ)^(n + 1) * ∑' j, (1/3:ℝ)^j := by
                rw [← tsum_mul_left]; congr 1; ext j; ring
            _ = (2:ℝ) * (1/3:ℝ)^(n + 1) * (1 - 1/3)⁻¹ := by rw [h1]
            _ = (1/3:ℝ)^n := by field_simp; ring
  rw [h_split, h_partial]
  have h_one_third_pow : (1/3:ℝ)^n = 1 / 3^n := by simp [div_eq_mul_inv]
  constructor
  · linarith
  · rw [← h_one_third_pow]
    exact add_le_add_right h_tail_bound _

/-- Existence of a binary-to-ternary function: g(x) = ∑ 2bⱼ 3^(-j). -/
lemma binaryToTernary_exists : ∃ g : ℝ → ℝ, BinaryToTernaryProperties g := by
  use binaryToTernaryFn
  exact {
    nonneg := by
      intro x
      simp only [binaryToTernaryFn]
      split_ifs with h
      · apply tsum_nonneg; intro j; positivity
      · rfl
    bounded := by
      intro x
      simp only [binaryToTernaryFn]
      split_ifs with h
      · have h_bound : ∀ j, (2 * binaryDigit x (j + 1) : ℝ) * (1/3:ℝ)^(j + 1) ≤
            (2:ℝ) * (1/3:ℝ)^(j + 1) := by
          intro j
          have h1 : (binaryDigit x (j + 1) : ℝ) ≤ 1 := by
            exact_mod_cast binaryDigit_le_one x (j + 1)
          nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/3) (j + 1)]
        have h_summable2 : Summable (fun j => (2:ℝ) * (1/3:ℝ)^(j + 1)) := by
          have h : Summable (fun j : ℕ => (1/3:ℝ)^j) :=
            summable_geometric_of_lt_one (by norm_num) (by norm_num)
          exact (h.mul_left 2).comp_injective (fun _ _ h => Nat.succ_injective h)
        calc ∑' j, (2 * binaryDigit x (j + 1) : ℝ) * (1/3:ℝ)^(j + 1)
            ≤ ∑' j, (2:ℝ) * (1/3:ℝ)^(j + 1) :=
              Summable.tsum_le_tsum h_bound (binaryToTernary_summable x) h_summable2
          _ = 1 := tsum_two_thirds_geometric
      · norm_num
    zero_outside := by
      intro x hx
      simp only [binaryToTernaryFn, if_neg hx]
    zero_at_zero := by
      simp only [binaryToTernaryFn]
      have h0 : (0:ℝ) ∈ Set.Icc 0 1 := ⟨le_refl 0, by norm_num⟩
      rw [if_pos h0]
      simp only [binaryDigit_zero, Nat.cast_zero, mul_zero, zero_mul, tsum_zero]
    zero_set_countable := by
      apply Set.Countable.mono _ (Set.countable_singleton 0)
      intro x hx
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff] at hx ⊢
      obtain ⟨hx_in, hgx⟩ := hx
      simp only [binaryToTernaryFn, if_pos hx_in] at hgx
      by_contra hx_ne
      have hx_pos : 0 < x := by
        rcases eq_or_lt_of_le hx_in.1 with rfl | hpos
        · exact absurd rfl hx_ne
        · exact hpos
      have h_exists_one : ∃ j, binaryDigit x (j + 1) = 1 := by
        by_cases hx1 : x = 1
        · exact ⟨0, by rw [hx1]; exact binaryDigit_one 1⟩
        · exact binaryDigit_exists_one_of_pos hx_pos (lt_of_le_of_ne hx_in.2 hx1)
      obtain ⟨j, hj_eq⟩ := h_exists_one
      have h_term_pos : (2 * binaryDigit x (j + 1) : ℝ) * (1/3:ℝ)^(j + 1) > 0 := by
        rw [hj_eq]; positivity
      have h_nonneg : ∀ k, 0 ≤ (2 * binaryDigit x (k + 1) : ℝ) * (1/3:ℝ)^(k + 1) := by
        intro k; positivity
      have h_sum_pos : 0 < ∑' k : ℕ, (2 * binaryDigit x (k + 1) : ℝ) * (1/3:ℝ)^(k + 1) :=
        (binaryToTernary_summable x).tsum_pos h_nonneg j h_term_pos
      linarith
    monotone_on := by
      intro x hx y hy hxy
      by_cases hxy' : x = y
      · simp [hxy']
      ·
        have hxy_strict : x < y := lt_of_le_of_ne hxy hxy'
        have hx_lt_one : x < 1 := lt_of_lt_of_le hxy_strict hy.2
        have hx_Ico : x ∈ Set.Ico (0:ℝ) 1 := ⟨hx.1, hx_lt_one⟩
        by_cases hy1 : y = 1
        ·
          subst hy1
          have h_exists_k : ∃ k, binaryDigit x (k + 1) = 0 := by
            by_contra h_all_one
            push_neg at h_all_one
            have h_all_eq_one : ∀ j, binaryDigit x (j + 1) = 1 := by
              intro j
              have h := binaryDigit_le_one x (j + 1)
              have hne := h_all_one j
              omega
            by_cases hx_dyadic : x ∈ DyadicRationals
            · simp only [DyadicRationals, Set.mem_setOf_eq] at hx_dyadic
              obtain ⟨k, n, hx_eq, _⟩ := hx_dyadic
              have h_zero_after : binaryDigit x (n + 1) = 0 := by
                simp only [binaryDigit, if_pos hx_Ico]
                rw [hx_eq]
                have h_calc : (2:ℝ)^(n + 1) * (k / (2:ℝ)^n) = 2 * k := by field_simp; ring
                rw [h_calc]
                have : (2 * k : ℝ) = ((2 * k : ℕ) : ℝ) := by simp
                rw [this, Nat.floor_natCast, Nat.mul_mod_right]
              exact h_all_one n h_zero_after
            · have hx_eq_sum := non_dyadic_eq_binary_sum hx_Ico hx_dyadic
              exfalso
              have h_sum_one : ∑' j : ℕ, (binaryDigit x (j + 1) : ℝ) * (1/2:ℝ)^(j + 1) = 1 := by
                have h_digit : ∀ j, (binaryDigit x (j + 1) : ℝ) = 1 := by
                  intro j; rw [h_all_eq_one j]; norm_num
                simp_rw [h_digit]
                have h := tsum_geometric_of_lt_one (r := (1:ℝ)/2) (by norm_num) (by norm_num)
                calc ∑' j, (1:ℝ) * (1/2)^(j + 1) = ∑' j, (1/2:ℝ)^(j + 1) := by simp
                  _ = (1/2) * ∑' j, (1/2:ℝ)^j := by
                      rw [← tsum_mul_left]; congr 1; ext j; ring
                  _ = (1/2) * (1 - 1/2)⁻¹ := by rw [h]
                  _ = 1 := by norm_num
              rw [hx_eq_sum, h_sum_one] at hx_lt_one
              linarith
          let k := Nat.find h_exists_k
          have hk_zero : binaryDigit x (k + 1) = 0 := Nat.find_spec h_exists_k
          have hk_first : ∀ j < k, binaryDigit x (j + 1) ≠ 0 := by
            intro j hj
            exact Nat.find_min h_exists_k hj
          have hk_lt : binaryDigit x (k + 1) < binaryDigit 1 (k + 1) := by
            rw [hk_zero, binaryDigit_one]; norm_num
          have hk_eq : ∀ j < k, binaryDigit x (j + 1) = binaryDigit 1 (j + 1) := by
            intro j hj
            rw [binaryDigit_one]
            have h := binaryDigit_le_one x (j + 1)
            have hne := hk_first j hj
            omega
          exact le_of_lt (binaryToTernary_lt_of_digit_lt hx ⟨zero_le_one, le_refl 1⟩ k hk_lt hk_eq)
        ·
          have hy_lt_one : y < 1 := lt_of_le_of_ne hy.2 hy1
          have hy_Ico : y ∈ Set.Ico (0:ℝ) 1 := ⟨hy.1, hy_lt_one⟩
          obtain ⟨k, hk_lt, hk_eq⟩ := binaryDigit_first_diff hx_Ico hy_Ico hxy_strict
          exact le_of_lt (binaryToTernary_lt_of_digit_lt hx hy k hk_lt hk_eq)
    image_in_cantor := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      simp only [binaryToTernaryFn, if_pos hx]
      let d : ℕ → ℕ := fun j => 2 * binaryDigit x (j + 1)
      have hd : ∀ j, d j ∈ ({0, 2} : Set ℕ) := by
        intro j
        have h := binaryDigit_le_one x (j + 1)
        simp only [d]
        interval_cases binaryDigit x (j + 1) <;> simp
      have hsum : Summable (fun j => (d j : ℝ) * (1/3:ℝ)^(j + 1)) := by
        convert binaryToTernary_summable x using 1
        funext j; simp [d]
      have hy_eq : ∑' j, (2:ℝ) * ↑(binaryDigit x (j + 1)) * (1 / 3) ^ (j + 1) =
          ∑' j, (d j : ℝ) * (1/3:ℝ)^(j + 1) := by
        congr 1; funext j; simp only [d, Nat.cast_mul, Nat.cast_ofNat]
      rw [hy_eq]
      exact mem_CantorSet_of_ternary_02 d hd hsum rfl
    injective_on_nonterminating := by
      let A := Set.Icc (0:ℝ) 1 \ DyadicRationals
      use A
      refine ⟨Set.diff_subset, ?_, ?_, ?_⟩
      · have h_sdiff : Set.Icc (0:ℝ) 1 \ A = DyadicRationals ∩ Set.Icc 0 1 := by
          simp only [A, Set.diff_diff_right, Set.diff_self, Set.empty_union, Set.inter_comm]
        rw [h_sdiff]
        exact DyadicRationals.countable.mono Set.inter_subset_left
      · intro x₁ hx₁ x₂ hx₂ heq
        simp only [A, Set.mem_diff] at hx₁ hx₂
        simp only [binaryToTernaryFn, if_pos hx₁.1, if_pos hx₂.1] at heq
        let d₁ : ℕ → ℕ := fun j => 2 * binaryDigit x₁ (j + 1)
        let d₂ : ℕ → ℕ := fun j => 2 * binaryDigit x₂ (j + 1)
        have hd₁ : ∀ j, d₁ j ∈ ({0, 2} : Set ℕ) := by
          intro j; have h := binaryDigit_le_one x₁ (j + 1)
          simp only [d₁]; interval_cases binaryDigit x₁ (j + 1) <;> simp
        have hd₂ : ∀ j, d₂ j ∈ ({0, 2} : Set ℕ) := by
          intro j; have h := binaryDigit_le_one x₂ (j + 1)
          simp only [d₂]; interval_cases binaryDigit x₂ (j + 1) <;> simp
        have heq' : ∑' j, (d₁ j : ℝ) * (1/3:ℝ)^(j + 1) = ∑' j, (d₂ j : ℝ) * (1/3:ℝ)^(j + 1) := by
          convert heq using 1 <;> { congr 1; funext j; simp only [d₁, d₂, Nat.cast_mul, Nat.cast_ofNat] }
        have hsum₁ : Summable (fun j => (d₁ j : ℝ) * (1/3:ℝ)^(j + 1)) := by
          convert binaryToTernary_summable x₁ using 1
          funext j; simp only [d₁, Nat.cast_mul, Nat.cast_ofNat]
        have hsum₂ : Summable (fun j => (d₂ j : ℝ) * (1/3:ℝ)^(j + 1)) := by
          convert binaryToTernary_summable x₂ using 1
          funext j; simp only [d₂, Nat.cast_mul, Nat.cast_ofNat]
        have hdigits_eq := ternary_02_expansion_unique hd₁ hd₂ hsum₁ hsum₂ heq'
        have hbinary_eq : ∀ j, binaryDigit x₁ (j + 1) = binaryDigit x₂ (j + 1) := by
          intro j
          have := hdigits_eq j
          simp only [d₁, d₂] at this
          omega
        have h1_dyadic : (1:ℝ) ∈ DyadicRationals := ⟨1, 0, by norm_num, by norm_num⟩
        have hx₁_ne_1 : x₁ ≠ 1 := fun h => hx₁.2 (h ▸ h1_dyadic)
        have hx₂_ne_1 : x₂ ≠ 1 := fun h => hx₂.2 (h ▸ h1_dyadic)
        have hx₁_Ico : x₁ ∈ Set.Ico (0:ℝ) 1 := ⟨hx₁.1.1, lt_of_le_of_ne hx₁.1.2 hx₁_ne_1⟩
        have hx₂_Ico : x₂ ∈ Set.Ico (0:ℝ) 1 := ⟨hx₂.1.1, lt_of_le_of_ne hx₂.1.2 hx₂_ne_1⟩
        apply eq_of_binaryDigit_eq_of_non_dyadic hx₁_Ico hx₂_Ico hx₁.2 hx₂.2
        intro j
        rcases j with _ | j
        ·
          simp only [binaryDigit, if_pos hx₁_Ico, if_pos hx₂_Ico, pow_zero, one_mul]
          have h1 : ⌊x₁⌋₊ = 0 := Nat.floor_eq_zero.mpr hx₁_Ico.2
          have h2 : ⌊x₂⌋₊ = 0 := Nat.floor_eq_zero.mpr hx₂_Ico.2
          simp [h1, h2]
        · exact hbinary_eq j
      · ext x
        simp only [A, Set.mem_inter_iff, Set.mem_diff, Set.mem_empty_iff_false, iff_false, not_and]
        intro ⟨_, hx_not_dyadic⟩ hx_dyadic
        exact hx_not_dyadic hx_dyadic
  }

end Remark_1_3_10
