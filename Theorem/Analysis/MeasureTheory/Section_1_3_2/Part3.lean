import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Def.Analysis.MeasureTheory.Section_1_3_2.Part3
set_option doc.verso.suggestions false


namespace UnsignedMeasurable.TFAE_helpers

variable {d : ℕ} {f : EuclideanSpace' d → EReal}

-- Key lemma: approx_fn takes values in {k/2^n : k = 0, 1, ..., n·2^n}
private lemma approx_fn_values (f : EuclideanSpace' d → EReal) (hf : Unsigned f) (n : ℕ) (x : EuclideanSpace' d) :
    ∃ k : ℕ, k ≤ n * 2^n ∧ approx_fn f n x = ((k : ℕ) : ℝ) / (2^n : ℝ) := by
  simp only [approx_fn]
  split_ifs with hnorm hbot htop hneg
  · -- t = ⊥ case (won't happen)
    use 0; simp
  · -- t = ⊤ case: min(f x, n) = ⊤ is impossible since min(f x, n) ≤ n
    exfalso
    have h1 : min (f x) ↑n ≤ ↑n := min_le_right _ _
    rw [htop] at h1
    exact not_le.mpr (EReal.coe_lt_top n) h1
  · -- r < 0 case (won't happen for unsigned)
    use 0; simp
  · -- normal case
    use ⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊
    constructor
    · -- Need to show floor ≤ n * 2^n
      have h_min_le : (min (f x) ↑n).toReal ≤ n := by
        have h1 : min (f x) ↑n ≤ ↑n := min_le_right _ _
        have h2 : min (f x) ↑n ≠ ⊤ := htop
        have h3 : min (f x) ↑n ≠ ⊥ := hbot
        have h4 : (↑n : EReal) ≠ ⊤ := EReal.coe_ne_top n
        exact EReal.toReal_le_toReal h1 h3 h4
      have h_prod_le : (min (f x) ↑n).toReal * 2^n ≤ (n : ℝ) * 2^n := by
        apply mul_le_mul_of_nonneg_right h_min_le
        exact pow_nonneg (by norm_num) n
      have h_nonneg : 0 ≤ (min (f x) ↑n).toReal * 2^n := by
        apply mul_nonneg
        · have h1 : 0 ≤ min (f x) ↑n := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
          exact EReal.toReal_nonneg h1
        · exact pow_nonneg (by norm_num) n
      have h_floor_le : (⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℝ) ≤ n * 2^n := by
        calc (⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℝ)
            ≤ (min (f x) ↑n).toReal * 2 ^ n := Nat.floor_le h_nonneg
          _ ≤ (n : ℝ) * 2^n := h_prod_le
      exact_mod_cast h_floor_le
    · rfl
  · -- |x| > n case
    use 0; simp

-- Helper: approx_fn is always nonnegative for unsigned functions
private lemma approx_fn_nonneg (f : EuclideanSpace' d → EReal) (_hf : Unsigned f)
    (n : ℕ) (x : EuclideanSpace' d) : approx_fn f n x ≥ 0 := by
  simp only [approx_fn]
  split_ifs with hnorm hbot htop hneg
  · exact le_refl 0  -- t = ⊥ case
  · exact EReal.coe_nonneg.mpr (Nat.cast_nonneg n)  -- t = ⊤ case
  · exact le_refl 0  -- r < 0 case
  · exact EReal.coe_nonneg.mpr (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) n))
  · exact le_refl 0  -- |x| > n case

-- Helper: floor approximation converges to the value as iSup
-- For r ≥ 0: r = ⨆ n, ⌊r * 2^n⌋₊ / 2^n (in EReal)
private lemma floor_approx_iSup_eq (r : ℝ) (hr : r ≥ 0) :
    (r : EReal) = ⨆ n : ℕ, (((⌊r * 2^n⌋₊ : ℕ) : ℝ) / (2^n : ℝ) : EReal) := by
  -- Define the approximating function for cleaner notation
  let f : ℕ → ℝ := fun n => ((⌊r * 2^n⌋₊ : ℕ) : ℝ) / (2^n : ℝ)
  change (r : EReal) = ⨆ n : ℕ, (f n : EReal)
  apply le_antisymm
  · -- Upper bound: r ≤ iSup
    apply EReal.le_of_forall_pos_le_add'
    intro ε hε
    -- Find N such that 1/2^N < ε using (1/2)^n → 0
    have h_tendsto : Filter.Tendsto (fun n : ℕ => ((1:ℝ)/2)^n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    rw [Metric.tendsto_atTop] at h_tendsto
    obtain ⟨N, hN⟩ := h_tendsto ε hε
    specialize hN N (le_refl N)
    simp only [Real.dist_eq, sub_zero, abs_of_pos (pow_pos (by norm_num : (0:ℝ) < 1/2) N)] at hN
    have h2N_pos : (2 : ℝ)^N > 0 := pow_pos (by norm_num) N
    have h_eps : (1 : ℝ) / 2^N < ε := by
      convert hN using 1
      rw [one_div, ← inv_pow, inv_eq_one_div]
    -- floor approx bound: r - 1/2^N < f N
    have h_floor_bound : r - 1/2^N < f N := by
      simp only [f]
      have h1 : r * 2^N - 1 < (⌊r * 2^N⌋₊ : ℝ) := Nat.sub_one_lt_floor (r * 2^N)
      calc r - 1/2^N = (r * 2^N - 1) / 2^N := by field_simp
           _ < (⌊r * 2^N⌋₊ : ℝ) / 2^N := by apply div_lt_div_of_pos_right h1 h2N_pos
    have h_le_iSup : (f N : EReal) ≤ ⨆ n : ℕ, (f n : EReal) := le_iSup_of_le N (le_refl _)
    -- r ≤ f N + ε
    have h3 : r ≤ f N + ε := by linarith
    calc (r : EReal) ≤ (f N + ε : ℝ) := EReal.coe_le_coe_iff.mpr h3
         _ = (f N : EReal) + (ε : EReal) := by rw [← EReal.coe_add]
         _ ≤ (⨆ n : ℕ, (f n : EReal)) + ε := add_le_add_left h_le_iSup ε
  · -- Lower bound: iSup ≤ r
    apply iSup_le
    intro n
    have h2n_pos : (2 : ℝ)^n > 0 := pow_pos (by norm_num) n
    have h_floor_le : f n ≤ r := by
      simp only [f]
      calc (⌊r * 2^n⌋₊ : ℝ) / 2^n ≤ (r * 2^n) / 2^n := by
             apply div_le_div_of_nonneg_right (Nat.floor_le (mul_nonneg hr (le_of_lt h2n_pos))) (le_of_lt h2n_pos)
           _ = r := by field_simp
    exact EReal.coe_le_coe_iff.mpr h_floor_le

-- Helper: approx_fn simplifies to floor formula when f x is finite and r ≤ n
private lemma approx_fn_eq_floor_when_finite (f : EuclideanSpace' d → EReal) (_hf : Unsigned f)
    (n : ℕ) (x : EuclideanSpace' d) (hn : ‖x‖ ≤ n) (r : ℝ) (hr : f x = r) (hr_nonneg : r ≥ 0)
    (hrn : r ≤ n) :
    approx_fn f n x = (((⌊r * 2^n⌋₊ : ℕ) : ℝ) / (2^n : ℝ) : EReal) := by
  simp only [approx_fn, hn, ite_true, hr]
  have h_min : min (r : EReal) n = r := min_eq_left (EReal.coe_le_coe_iff.mpr hrn)
  have h_min_ne_bot : min (r : EReal) n ≠ ⊥ := by simp [h_min, EReal.coe_ne_bot]
  have h_min_ne_top : min (r : EReal) n ≠ ⊤ := by simp [h_min, EReal.coe_ne_top]
  have h_toReal : (min (r : EReal) n).toReal = r := by
    simp [h_min, EReal.toReal_coe]
  have h_nonneg : ¬(min (r : EReal) n).toReal < 0 := by simp [h_toReal, hr_nonneg]
  simp only [h_min_ne_bot, ite_false, h_min_ne_top, h_toReal]
  simp only [not_lt.mpr hr_nonneg, ite_false]

-- Helper: (n * 2^n) / 2^n = n in EReal
private lemma mul_pow2_div_pow2_eq (n : ℕ) :
    ((n * 2^n : ℕ) : EReal) / ((2^n : ℕ) : EReal) = ((n : ℕ) : EReal) := by
  have h2n_ne : (2^n : ℕ) ≠ 0 := pow_ne_zero n (by norm_num)
  have h2n_ne_bot : ((2^n : ℕ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have h2n_ne_top : ((2^n : ℕ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have h2n_ne_zero : ((2^n : ℕ) : EReal) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact h2n_ne
  rw [show ((n * 2^n : ℕ) : EReal) = ((n : ℕ) : EReal) * ((2^n : ℕ) : EReal) by push_cast; ring_nf]
  rw [mul_div_assoc, EReal.div_self h2n_ne_bot h2n_ne_top h2n_ne_zero, mul_one]

-- Helper: Extract equality from EReal division equality with 2^n denominator
private lemma ereal_div_pow2_eq_imp_eq (j k n : ℕ)
    (h : (((j : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) =
         (((k : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal)) :
    j = k := by
  have h2n_pos : (0 : ℝ) < 2^n := pow_pos (by norm_num) n
  have h2n_ne : ((2^n : ℕ) : ℝ) ≠ 0 := by positivity
  have h_real : ((j : ℕ) : ℝ) / (2^n : ℕ) = ((k : ℕ) : ℝ) / (2^n : ℕ) := by
    have hlhs : (((j : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) =
                (((j : ℕ) : ℝ) / ((2^n : ℕ) : ℝ) : EReal) := by norm_cast
    have hrhs : (((k : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) =
                (((k : ℕ) : ℝ) / ((2^n : ℕ) : ℝ) : EReal) := by norm_cast
    rw [hlhs, hrhs] at h
    exact EReal.coe_eq_coe_iff.mp h
  have h_eq : ((j : ℕ) : ℝ) = ((k : ℕ) : ℝ) := by
    rw [div_eq_div_iff h2n_ne h2n_ne] at h_real
    exact mul_right_cancel₀ h2n_ne h_real
  exact Nat.cast_injective h_eq

-- Each level set of approx_fn is LebesgueMeasurable
-- The key observation: level sets are Boolean combinations of:
-- - {‖x‖ ≤ n} which is closed, hence LebesgueMeasurable
-- - {‖x‖ > n} which is open, hence LebesgueMeasurable
-- - {f x ≥ t} which is LebesgueMeasurable by hvi
-- - {f x < t} which is LebesgueMeasurable by hvii
private lemma approx_fn_levelset_LebesgueMeasurable (hf : Unsigned f) (hvi : stmt_vi f)
    (hvii : stmt_vii f) (n : ℕ) (v : EReal) :
    LebesgueMeasurable {x | approx_fn f n x = v} := by
  -- Helper: ball and outside ball are Lebesgue measurable
  have ball_leb : LebesgueMeasurable {x : EuclideanSpace' d | ‖x‖ ≤ (n : ℝ)} := normBall_LebesgueMeasurable n
  have outside_leb : LebesgueMeasurable {x : EuclideanSpace' d | ‖x‖ > (n : ℝ)} :=
    (isOpen_lt continuous_const continuous_norm).measurable

  by_cases hv_range : v ∈ Set.range (approx_fn f n)
  swap
  · -- v not in range: level set is empty
    convert LebesgueMeasurable.empty
    ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h; exact hv_range ⟨x, h⟩

  -- v is in range: the level set is a Boolean combination of measurable sets
  -- Decompose into inside/outside ball
  have h_split : {x | approx_fn f n x = v} =
      ({x | ‖x‖ ≤ (n:ℝ)} ∩ {x | approx_fn f n x = v}) ∪
      ({x | ‖x‖ > (n:ℝ)} ∩ {x | approx_fn f n x = v}) := by
    ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    by_cases h : ‖x‖ ≤ n <;> simp [h, lt_of_not_ge]
  rw [h_split]
  apply LebesgueMeasurable.union

  -- Inside ball case: Show {‖x‖ ≤ n} ∩ {approx_fn = v} is LebesgueMeasurable
  -- Strategy: Show this is a Boolean combination of:
  -- - {‖x‖ ≤ n} which is LebesgueMeasurable (closed ball)
  -- - {f x ≥ t} for various thresholds t (LebesgueMeasurable by hvi)
  -- - {f x < t} for various thresholds t (LebesgueMeasurable by hvii)
  · obtain ⟨x₀, hx₀⟩ := hv_range
    obtain ⟨k, hk_bound, hk_eq⟩ := approx_fn_values f hf n x₀
    have hv_eq : v = ((k : ℕ) : ℝ) / (2^n : ℝ) := by rw [← hx₀, hk_eq]
    have h2n_pos : (0 : ℝ) < 2^n := pow_pos (by norm_num) n
    have h2n_ne : (2^n : ℝ) ≠ 0 := ne_of_gt h2n_pos
    by_cases hk_max : k = n * 2^n
    · -- k = n * 2^n: level set inside ball equals {‖x‖ ≤ n} ∩ {f x ≥ n}
      have hv_eq_n : v = n := by
        rw [hv_eq, hk_max]
        conv_lhs => rw [show ((n * 2^n : ℕ) : ℝ) = (n : ℝ) * 2^n by simp [Nat.cast_mul, Nat.cast_pow]]
        rw [← EReal.coe_div]; congr 1; field_simp
      have h_eq : {x | ‖x‖ ≤ (n:ℝ)} ∩ {x | approx_fn f n x = v} =
          {x | ‖x‖ ≤ n} ∩ {x | f x ≥ (n : EReal)} := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · intro ⟨hnorm, hval⟩
          rw [hv_eq_n] at hval
          refine ⟨hnorm, ?_⟩
          simp only [approx_fn, hnorm, ite_true] at hval
          split_ifs at hval with hbot htop hneg
          · exfalso
            have h_min_ge : min (f x) ↑n ≥ 0 := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
            rw [hbot] at h_min_ge; exact not_le.mpr EReal.bot_lt_zero h_min_ge
          · grind
          · exfalso
            have h_min_ge : min (f x) ↑n ≥ 0 := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
            exact not_le.mpr hneg (EReal.toReal_nonneg h_min_ge)
          · -- floor(...)/2^n = n means floor(...) = n*2^n
            -- First normalize the coercions in hval
            have hval' : (((⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℕ) : ℝ) / (2^n : ℝ) : EReal) = (n : EReal) := by
              have h1 : ((2^n : ℕ) : EReal) = ((2^n : ℕ) : ℝ) := EReal.coe_natCast.symm
              have h2 : ((⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℕ) : EReal) =
                  ((⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℕ) : ℝ) := EReal.coe_natCast.symm
              simp only [← EReal.coe_div] at hval; exact hval
            have h_coe := EReal.coe_eq_coe_iff.mp hval'
            have h_floor : ⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ = n * 2^n := by
              field_simp at h_coe
              have h_coe' : (⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℝ) = ((n * 2^n : ℕ) : ℝ) := by
                push_cast; linarith
              exact Nat.cast_injective h_coe'
            have h_min_nonneg : min (f x) ↑n ≥ 0 := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
            have h_prod_nonneg := mul_nonneg (EReal.toReal_nonneg h_min_nonneg) (le_of_lt h2n_pos)
            have h_prod_ge : (min (f x) ↑n).toReal * 2^n ≥ n * 2^n := by
              have := Nat.floor_le h_prod_nonneg; rw [h_floor] at this; exact_mod_cast this
            have h_toReal_ge : (min (f x) ↑n).toReal ≥ n := by nlinarith
            have h_min_le : (min (f x) ↑n).toReal ≤ n := by
              have h_le := min_le_right (f x) ↑n
              have := EReal.toReal_le_toReal h_le hbot (EReal.coe_ne_top n)
              have hto : (↑n : EReal).toReal = n := by norm_cast
              simpa [hto] using this
            have h_min_eq_n : (min (f x) ↑n).toReal = n := le_antisymm h_min_le h_toReal_ge
            by_contra hcontra; push_neg at hcontra
            have h_min_eq : min (f x) ↑n = f x := min_eq_left (le_of_lt hcontra)
            rw [h_min_eq] at h_min_eq_n
            have h_fx_ne_top : f x ≠ ⊤ := by intro heq; rw [heq] at hcontra; exact not_lt.mpr le_top hcontra
            have h_fx_ne_bot : f x ≠ ⊥ := by intro heq; rw [h_min_eq] at hbot; exact hbot heq
            rw [← EReal.coe_toReal h_fx_ne_top h_fx_ne_bot] at hcontra
            have hcontra' : (f x).toReal < (n : ℝ) := EReal.coe_lt_coe_iff.mp hcontra
            rw [h_min_eq_n] at hcontra'
            exact lt_irrefl (n : ℝ) hcontra'
        · intro ⟨hnorm, hfx_ge⟩
          refine ⟨hnorm, ?_⟩
          simp only [approx_fn, hnorm, ite_true]
          have h_min_eq : min (f x) ↑n = ↑n := min_eq_right hfx_ge
          split_ifs with hbot htop hneg
          · exfalso; rw [h_min_eq] at hbot; exact EReal.coe_ne_bot n hbot
          · exfalso; rw [h_min_eq] at htop; exact EReal.coe_ne_top n htop
          · exfalso; rw [h_min_eq] at hneg
            have h_toReal : (↑n : EReal).toReal = (n : ℝ) := by
              rw [show (↑n : EReal) = ↑(n : ℝ) from EReal.coe_natCast.symm, EReal.toReal_coe]
            rw [h_toReal] at hneg; exact not_lt.mpr (Nat.cast_nonneg n) hneg
          · rw [h_min_eq, hv_eq_n]
            have h_toReal : (↑n : EReal).toReal = (n : ℝ) := by
              rw [show (↑n : EReal) = ↑(n : ℝ) from EReal.coe_natCast.symm, EReal.toReal_coe]
            rw [h_toReal]
            have h_floor : ⌊(n : ℝ) * 2 ^ n⌋₊ = n * 2^n := by
              rw [show ((n : ℕ) : ℝ) * 2 ^ n = ((n * 2^n : ℕ) : ℝ) by
                simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]]
              exact Nat.floor_natCast (n * 2^n)
            rw [h_floor]
            -- Goal: ↑↑(n * 2 ^ n) / ↑(2 ^ n) = ↑n
            -- Use EReal.coe_natCast to normalize coercions
            simp only [← EReal.coe_natCast, ← EReal.coe_div, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
            grind
      rw [h_eq]
      exact ball_leb.inter (hvi n)
    · -- k < n * 2^n: level set is {‖x‖ ≤ n} ∩ {f x ≥ k/2^n} ∩ {f x < (k+1)/2^n}
      have hk_lt : k < n * 2^n := Nat.lt_of_le_of_ne hk_bound hk_max
      have h_le := hvi (((k : ℕ) : ℝ) / (2^n : ℝ))
      have h_lt := hvii ((((k + 1) : ℕ) : ℝ) / (2^n : ℝ))
      have h_eq : {x | ‖x‖ ≤ (n:ℝ)} ∩ {x | approx_fn f n x = v} =
          {x | ‖x‖ ≤ n} ∩ ({x | f x ≥ (((k : ℕ) : ℝ) / (2^n : ℝ) : EReal)} ∩
          {x | f x < ((((k + 1) : ℕ) : ℝ) / (2^n : ℝ) : EReal)}) := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · intro ⟨hnorm, hval⟩
          rw [hv_eq] at hval
          simp only [approx_fn, hnorm, ite_true] at hval
          split_ifs at hval with hbot htop hneg
          · exfalso
            have h_min_ge : min (f x) ↑n ≥ 0 := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
            rw [hbot] at h_min_ge; exact not_le.mpr EReal.bot_lt_zero h_min_ge
          · exact absurd (htop ▸ min_le_right (f x) (↑n : EReal)) (not_le.mpr (EReal.coe_lt_top n))
          · exfalso
            have h_min_ge : min (f x) ↑n ≥ 0 := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
            exact not_le.mpr hneg (EReal.toReal_nonneg h_min_ge)
          · -- Normal case: Show floor = k and derive bounds
            have hval' : (((⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℕ) : ℝ) / (2^n : ℝ) : EReal) =
                (((k : ℕ) : ℝ) / (2^n : ℝ) : EReal) := by
              have h1 : ((2^n : ℕ) : EReal) = ((2^n : ℕ) : ℝ) := EReal.coe_natCast.symm
              have h2 : ((⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℕ) : EReal) =
                  ((⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ : ℕ) : ℝ) := EReal.coe_natCast.symm
              have h3 : ((k : ℕ) : EReal) = ((k : ℕ) : ℝ) := EReal.coe_natCast.symm
              simp only [← EReal.coe_div] at hval; exact hval
            have h_coe := EReal.coe_eq_coe_iff.mp hval'
            have h_floor : ⌊(min (f x) ↑n).toReal * 2 ^ n⌋₊ = k := by
              field_simp at h_coe; exact Nat.cast_injective h_coe
            have h_min_nonneg : min (f x) ↑n ≥ 0 := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
            have h_prod_nonneg := mul_nonneg (EReal.toReal_nonneg h_min_nonneg) (le_of_lt h2n_pos)
            -- Get bounds on (min (f x) n).toReal
            have h_ge : (min (f x) ↑n).toReal ≥ (k : ℝ) / 2^n := by
              have := Nat.floor_le h_prod_nonneg; rw [h_floor] at this
              calc (k : ℝ) / 2^n = (k : ℝ) * (2^n)⁻¹ := by ring
                _ ≤ (min (f x) ↑n).toReal * 2^n * (2^n)⁻¹ := by
                  apply mul_le_mul_of_nonneg_right this (inv_nonneg.mpr (le_of_lt h2n_pos))
                _ = (min (f x) ↑n).toReal := by field_simp
            have h_lt' : (min (f x) ↑n).toReal * 2^n < k + 1 := by
              have := Nat.lt_floor_add_one ((min (f x) ↑n).toReal * 2^n)
              rw [h_floor] at this; exact_mod_cast this
            have h_toReal_lt : (min (f x) ↑n).toReal < ((k + 1) : ℝ) / 2^n := by
              calc (min (f x) ↑n).toReal = (min (f x) ↑n).toReal * 2^n / 2^n := by field_simp
                _ < ((k + 1) : ℝ) / 2^n := div_lt_div_of_pos_right h_lt' h2n_pos
            -- Show (k+1)/2^n ≤ n
            have h_val_le_n : ((k + 1) : ℝ) / 2^n ≤ n := by
              have h1 : (k + 1 : ℕ) ≤ n * 2^n := by omega
              have h1' : ((k + 1) : ℝ) ≤ (n * 2^n : ℝ) := by exact_mod_cast h1
              calc ((k + 1) : ℝ) / 2^n ≤ (n * 2^n : ℝ) / 2^n := div_le_div_of_nonneg_right h1' (le_of_lt h2n_pos)
                _ = n := by field_simp
            have h_fx_lt_n : f x < ↑n := by
              by_cases h_fx_le_n : f x ≤ n
              · have h_min_eq : min (f x) ↑n = f x := min_eq_left h_fx_le_n
                rw [h_min_eq] at h_toReal_lt
                by_cases h_fx_top : f x = ⊤
                · rw [h_fx_top] at h_fx_le_n; exact absurd h_fx_le_n (not_le.mpr (EReal.coe_lt_top n))
                · have h_fx_ne_bot : f x ≠ ⊥ := by intro heq; rw [h_min_eq] at hbot; exact hbot heq
                  rw [← EReal.coe_toReal h_fx_top h_fx_ne_bot]
                  rw [show (↑n : EReal) = ↑(n : ℝ) from EReal.coe_natCast.symm]
                  rw [EReal.coe_lt_coe_iff]
                  have h_k1_eq : (↑k + 1 : ℝ) = ((k + 1) : ℕ) := by simp only [Nat.cast_add, Nat.cast_one]
                  have h_val_le_n' : ((k + 1) : ℕ) / 2^n ≤ (n : ℝ) := by rw [← h_k1_eq]; exact h_val_le_n
                  calc (f x).toReal < (↑k + 1) / 2^n := h_toReal_lt
                    _ = ((k + 1) : ℕ) / 2^n := by rw [h_k1_eq]
                    _ ≤ n := h_val_le_n'
              · -- h_fx_le_n : ¬(f x ≤ n), i.e., n < f x
                push_neg at h_fx_le_n
                -- min(f x, n) = n when f x > n
                have h_min : min (f x) ↑n = ↑n := min_eq_right (le_of_lt h_fx_le_n)
                -- h_toReal_lt : (min (f x) n).toReal < (↑k + 1) / 2^n
                -- Becomes: n.toReal < (↑k + 1) / 2^n
                rw [h_min] at h_toReal_lt
                have h_n_toReal : (↑n : EReal).toReal = (n : ℝ) := by
                  rw [show (↑n : EReal) = ↑(n : ℝ) from EReal.coe_natCast.symm, EReal.toReal_coe]
                rw [h_n_toReal] at h_toReal_lt
                exfalso; linarith [h_val_le_n]
            have h_min_eq : min (f x) ↑n = f x := min_eq_left (le_of_lt h_fx_lt_n)
            rw [h_min_eq] at h_ge h_toReal_lt
            have h_fx_ne_top : f x ≠ ⊤ := by intro heq; rw [heq] at h_fx_lt_n; exact not_lt.mpr le_top h_fx_lt_n
            have h_fx_ne_bot : f x ≠ ⊥ := by intro heq; rw [h_min_eq] at hbot; exact hbot heq
            refine ⟨hnorm, ?_, ?_⟩
            · -- Show f x ≥ k / 2^n
              rw [← EReal.coe_toReal h_fx_ne_top h_fx_ne_bot]
              have hk_coe : ((k : ℕ) : EReal) = ((k : ℕ) : ℝ) := EReal.coe_natCast.symm
              have h2n_coe : ((2^n : ℕ) : EReal) = ((2^n : ℕ) : ℝ) := EReal.coe_natCast.symm
              simp only [← EReal.coe_div, ge_iff_le, EReal.coe_le_coe_iff]; exact h_ge
            · -- Show f x < (k + 1) / 2^n
              rw [← EReal.coe_toReal h_fx_ne_top h_fx_ne_bot]
              have h_k1_eq : (↑k + 1 : ℝ) = ((k + 1) : ℕ) := by simp only [Nat.cast_add, Nat.cast_one]
              have h_toReal_lt' : (f x).toReal < ((k + 1) : ℕ) / 2^n := by rw [← h_k1_eq]; exact h_toReal_lt
              simp only [← EReal.coe_div, EReal.coe_lt_coe_iff]; exact h_toReal_lt'
        · intro ⟨hnorm, hfx_ge, hfx_lt⟩
          refine ⟨hnorm, ?_⟩
          rw [hv_eq]; simp only [approx_fn, hnorm, ite_true]
          -- From hfx_lt: f x < (k+1)/2^n ≤ n, so min(f x, n) = f x
          have h_val_le_n : ((k + 1) : ℝ) / 2^n ≤ n := by
            have h1 : (k + 1 : ℕ) ≤ n * 2^n := by omega
            have h1' : ((k + 1) : ℝ) ≤ (n * 2^n : ℝ) := by exact_mod_cast h1
            calc ((k + 1) : ℝ) / 2^n ≤ (n * 2^n : ℝ) / 2^n := div_le_div_of_nonneg_right h1' (le_of_lt h2n_pos)
              _ = n := by field_simp
          have h_fx_lt_n : f x < ↑n := by
            -- f x < ↑↑(k+1) / ↑(2^n) and (k+1)/2^n ≤ n, so f x < n
            -- h_in_real lifts h_val_le_n to the correct form
            have h_in_real : (((k + 1 : ℕ) : ℝ) / ((2^n : ℕ) : ℝ)) ≤ (n : ℝ) := by
              simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
              exact h_val_le_n
            -- Use refine to infer goal type from hfx_lt (which has ↑(2^n) as coerced Nat)
            refine lt_of_lt_of_le hfx_lt ?h_bound
            -- Goal now: ↑↑(k+1) / ↑(2^n) ≤ ↑n (with ↑(2^n) as coerced Nat!)
            case h_bound =>
              simp_rw [EReal.coe_natCast.symm, ← EReal.coe_div, EReal.coe_le_coe_iff]
              convert h_in_real using 2
              -- Goal: 2 ^ n = ↑(2 ^ n) in ℝ - Real power vs coerced Nat power
              simp only [Nat.cast_pow, Nat.cast_ofNat]
          have h_min_eq : min (f x) ↑n = f x := min_eq_left (le_of_lt h_fx_lt_n)
          rw [h_min_eq]
          have h_fx_ne_top : f x ≠ ⊤ := by intro heq; rw [heq] at h_fx_lt_n; exact not_lt.mpr le_top h_fx_lt_n
          have h_fx_ne_bot : f x ≠ ⊥ := fun heq => not_le.mpr EReal.bot_lt_zero (heq ▸ hf x)
          split_ifs with hbot' htop'
          · exfalso; exact h_fx_ne_bot hbot'
          · exfalso
            have h_fx_ge : f x ≥ 0 := hf x
            exact not_lt.mpr (EReal.toReal_nonneg h_fx_ge) htop'
          · -- Show floor((f x).toReal * 2^n) = k
            rw [← EReal.coe_div] at hfx_ge hfx_lt
            have h_ge' : (f x).toReal ≥ (k : ℝ) / 2^n := by
              rw [← EReal.coe_toReal h_fx_ne_top h_fx_ne_bot] at hfx_ge
              exact EReal.coe_le_coe_iff.mp hfx_ge
            have h_lt' : (f x).toReal < ((k + 1) : ℝ) / 2^n := by
              rw [← EReal.coe_toReal h_fx_ne_top h_fx_ne_bot] at hfx_lt
              rw [Nat.cast_add_one] at hfx_lt
              exact EReal.coe_lt_coe_iff.mp hfx_lt
            have h_prod_ge : (f x).toReal * 2^n ≥ k := by
              calc (f x).toReal * 2^n ≥ ((k : ℝ) / 2^n) * 2^n := by nlinarith
                _ = k := by field_simp
            have h_prod_lt : (f x).toReal * 2^n < k + 1 := by
              calc (f x).toReal * 2^n < (((k + 1) : ℝ) / 2^n) * 2^n := by nlinarith
                _ = k + 1 := by field_simp
            have h_floor : ⌊(f x).toReal * 2 ^ n⌋₊ = k := by
              have h_nonneg : 0 ≤ (f x).toReal * 2 ^ n := by
                apply mul_nonneg
                · exact EReal.toReal_nonneg (hf x)
                · exact pow_nonneg (by norm_num) n
              rw [Nat.floor_eq_iff h_nonneg]
              constructor <;> linarith
            have h1 : ((2^n : ℕ) : EReal) = ((2^n : ℕ) : ℝ) := EReal.coe_natCast.symm
            have h2 : ((k : ℕ) : EReal) = ((k : ℕ) : ℝ) := EReal.coe_natCast.symm
            simp only [h_floor, ← EReal.coe_div]
      rw [h_eq]
      exact ball_leb.inter (h_le.inter h_lt)

  -- Outside ball case: {‖x‖ > n} ∩ {approx_fn = v} = {‖x‖ > n} if v = 0, else ∅
  · have h_eq : {x | ‖x‖ > (n:ℝ)} ∩ {x | approx_fn f n x = v} =
        if v = 0 then {x | ‖x‖ > (n:ℝ)} else ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, approx_fn]
      constructor
      · intro ⟨hn, hv⟩
        have hn' : ¬ ‖x‖ ≤ (n:ℝ) := not_le.mpr hn
        simp only [hn', ite_false] at hv
        split_ifs <;> [exact hn; exact absurd hv.symm ‹_›]
      · intro h
        split_ifs at h with hv0
        · have hn : ‖x‖ > (n:ℝ) := h
          have hn' : ¬ ‖x‖ ≤ (n:ℝ) := not_le.mpr hn
          exact ⟨hn, by simp only [hn', ite_false, hv0]⟩
        · exact absurd h id
    rw [h_eq]
    split_ifs <;> [exact outside_leb; exact LebesgueMeasurable.empty]

-- The main construction lemma
private lemma v_to_xi_imp_iv (hf : Unsigned f) (hvi : stmt_vi f) (hvii : stmt_vii f) :
    stmt_iv f := by
  -- Construct f_n(x) = largest k·2^{-n} ≤ min(f(x), n) when |x| ≤ n, else 0
  use approx_fn f
  constructor
  · -- Each approx_fn f n is a simple function, bounded, with finite measure support
    intro n
    constructor
    · -- UnsignedSimpleFunction (approx_fn f n)
      -- Strategy: use the indicator sum representation directly
      -- approx_fn f n = sum over k from 0 to n*2^n of (k/2^n) • indicator{approx_fn f n = k/2^n}
      let K := n * 2^n + 1
      let c : Fin K → EReal := fun i => if i.val = n * 2^n then n else ((i.val : ℕ) : ℝ) / (2^n : ℝ)
      let E : Fin K → Set (EuclideanSpace' d) := fun i => {x | approx_fn f n x = c i}
      use K, c, E
      constructor
      · intro i
        constructor
        · -- LebesgueMeasurable (E i) - Use the helper lemma
          simp only [E]
          exact approx_fn_levelset_LebesgueMeasurable hf hvi hvii n (c i)
        · -- c i ≥ 0
          simp only [c]
          split_ifs with hi
          · exact EReal.coe_nonneg.mpr (Nat.cast_nonneg n)
          · have h2n_pos : (2^n : ℝ) > 0 := pow_pos (by norm_num) n
            have h_nonneg : (0 : ℝ) ≤ (i.val : ℝ) / 2^n := div_nonneg (Nat.cast_nonneg i.val) (le_of_lt h2n_pos)
            exact EReal.coe_nonneg.mpr h_nonneg
      · -- approx_fn f n = sum c i • indicator (E i)
        ext x
        simp only [Finset.sum_apply, Pi.smul_apply, EReal.indicator]
        -- Find which i has x ∈ E i
        obtain ⟨k, hk_bound, hk_eq⟩ := approx_fn_values f hf n x
        have h_unique : ∃! i : Fin K, x ∈ E i := by
          by_cases hk_max : k = n * 2^n
          · use ⟨n * 2^n, by omega⟩
            simp only [E, c, Set.mem_setOf_eq]
            constructor
            · simp only [hk_max] at hk_eq
              simp only [ite_true]
              rw [hk_eq]
              -- Use helper lemma, then normalize coercions
              convert mul_pow2_div_pow2_eq n using 2 <;> norm_cast
            · intro j hj
              -- hj : approx_fn f n x = if ↑j = n * 2^n then ↑n else ↑↑↑j / ↑(2^n)
              -- The simp didn't make progress because E is not in scope for hj after previous simp
              ext; simp only
              by_cases hj_max : j.val = n * 2^n
              · exact hj_max
              · -- j.val ≠ n*2^n, but we'll show they must be equal from hj and hk_eq
                simp only [hj_max, ↓reduceIte] at hj
                rw [hk_max] at hk_eq
                exfalso; apply hj_max
                have h_eq_ereal : (((j.val : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) =
                                  (((n * 2^n : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) := by
                  convert hj.symm.trans hk_eq using 2 <;> norm_cast
                exact ereal_div_pow2_eq_imp_eq j.val (n * 2^n) n h_eq_ereal
          · use ⟨k, by omega⟩
            simp only [E, c, Set.mem_setOf_eq]
            constructor
            · have h_c_val : (if k = n * 2^n then (n : EReal) else ((k : ℕ) : ℝ) / (2^n : ℝ)) = ((k : ℕ) : ℝ) / (2^n : ℝ) := by simp [hk_max]
              simp only [h_c_val]
              exact hk_eq
            · intro j hj
              -- hj already has the expanded form after intro
              ext
              by_cases hj_max : j.val = n * 2^n
              · -- j.val = n*2^n but k ≠ n*2^n: k/2^n = n = (n*2^n)/2^n, contradiction
                simp only [hj_max, ↓reduceIte] at hj
                have h_k_val : (((k : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) = (n : EReal) := by
                  convert hk_eq.symm.trans hj using 2; all_goals norm_cast
                have h_eq : (((k : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) =
                            (((n * 2^n : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) := by
                  rw [h_k_val]; convert (mul_pow2_div_pow2_eq n).symm using 2 <;> norm_cast
                exact absurd (ereal_div_pow2_eq_imp_eq k (n * 2^n) n h_eq) hk_max
              · -- Both j and k are not n*2^n
                simp only [hj_max, ↓reduceIte] at hj
                have h_eq' : (((j.val : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) =
                             (((k : ℕ) : ℝ) : EReal) / ((2^n : ℕ) : EReal) := by
                  convert hj.symm.trans hk_eq using 2 <;> norm_cast
                exact ereal_div_pow2_eq_imp_eq j.val k n h_eq'
        -- Now use the unique i to simplify the sum
        have h_mem : x ∈ E (h_unique.choose) := h_unique.choose_spec.1
        rw [Finset.sum_eq_single h_unique.choose]
        · -- h_mem : x ∈ E (h_unique.choose) means approx_fn f n x = c (h_unique.choose)
          -- indicator = 1, so goal is approx_fn f n x = c (...) • 1 = c (...)
          simp only [Real.EReal_fun, Set.indicator'_of_mem h_mem, EReal.coe_one, smul_eq_mul, mul_one]
          exact h_mem
        · intro b hb_mem hb_ne
          have h_not_mem : x ∉ E b := by
            intro hcontra
            have h_eq := h_unique.choose_spec.2 b hcontra
            exact hb_ne h_eq
          simp only [Real.EReal_fun, Set.indicator'_of_notMem h_not_mem,
                     EReal.coe_zero, smul_zero]
        · intro hcontra
          exact absurd (Finset.mem_univ _) hcontra
    constructor
    · -- EReal.BoundedFunction (approx_fn f n)
      use n
      intro x
      obtain ⟨k, hk_bound, hk_eq⟩ := approx_fn_values f hf n x
      rw [hk_eq]
      have h2n_pos : (2^n : ℝ) > 0 := pow_pos (by norm_num) n
      have h2n_nonneg : (0 : ℝ) ≤ 2^n := le_of_lt h2n_pos
      have h_val_nonneg : (0 : ℝ) ≤ (k : ℝ) / 2^n := div_nonneg (Nat.cast_nonneg k) h2n_nonneg
      have h_val_le_n : (k : ℝ) / 2^n ≤ n := by
        have h1 : (k : ℝ) ≤ n * 2^n := by exact_mod_cast hk_bound
        calc (k : ℝ) / 2^n ≤ (n * 2^n) / 2^n := by apply div_le_div_of_nonneg_right h1 h2n_nonneg
          _ = n := by field_simp
      -- The value k/2^n as a real
      let val : ℝ := (k : ℝ) / 2^n
      -- Direct proof - just use native simp with the relevant lemmas
      simp only [← EReal.coe_div, EReal.abs_def, abs_of_nonneg h_val_nonneg]
      calc ENNReal.ofReal val
        ≤ ENNReal.ofReal n := ENNReal.ofReal_le_ofReal h_val_le_n
        _ = ↑n := ENNReal.ofReal_natCast n
    · -- FiniteMeasureSupport (approx_fn f n)
      -- Support ⊆ {|x| ≤ n}, which has finite Lebesgue measure
      -- Closed balls are compact, so have finite measure
      have h_support_sub : Support (approx_fn f n) ⊆ {x | ‖x‖ ≤ n} := by
        intro x hx
        simp only [Support] at hx
        by_contra h
        simp only [Set.mem_setOf_eq, not_le] at h
        -- When ‖x‖ > n, approx_fn f n x = 0
        have h' : ¬(‖x‖ ≤ (n : ℝ)) := not_le.mpr h
        have h_eq : approx_fn f n x = 0 := by
          unfold approx_fn
          simp only [h', ite_false]
        exact hx h_eq
      have h_ball_eq : {x : EuclideanSpace' d | ‖x‖ ≤ n} = Metric.closedBall 0 n := by
        ext x; simp [Metric.closedBall, dist_zero_right]
      have h_compact : IsCompact (Metric.closedBall (0 : EuclideanSpace' d) n) :=
        isCompact_closedBall 0 n
      have h_finite : Lebesgue_outer_measure (Metric.closedBall (0 : EuclideanSpace' d) n) ≠ ⊤ :=
        Lebesgue_outer_measure.finite_of_compact h_compact
      calc Lebesgue_measure (Support (approx_fn f n))
          ≤ Lebesgue_measure {x | ‖x‖ ≤ n} := Lebesgue_outer_measure.mono h_support_sub
        _ = Lebesgue_measure (Metric.closedBall 0 n) := by rw [h_ball_eq]
        _ < ⊤ := lt_top_iff_ne_top.mpr h_finite
  constructor
  · -- Monotonicity: approx_fn f m x ≤ approx_fn f n x for m ≤ n
    intro x m n hmn
    -- Key insight: as n increases, the ball grows and approximation gets finer
    unfold approx_fn
    by_cases hm : ‖x‖ ≤ m
    · -- |x| ≤ m ≤ n
      have hn : ‖x‖ ≤ n := le_trans (by exact_mod_cast hm) (Nat.cast_le.mpr hmn)
      simp only [hm, hn, ite_true]
      -- Both are non-trivial, need to compare the floor values
      -- approx_fn f m x approximates min(f x, m) and approx_fn f n x approximates min(f x, n)
      -- Since min(f x, m) ≤ min(f x, n) and approximation gets better, we have monotonicity
      -- First eliminate the impossible cases using unsigned property
      have hm_ne_bot : min (f x) ↑m ≠ ⊥ := by
        intro h
        have h1 : 0 ≤ min (f x) ↑m := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg m))
        rw [h] at h1; exact not_le.mpr EReal.bot_lt_zero h1
      have hn_ne_bot : min (f x) ↑n ≠ ⊥ := by
        intro h
        have h1 : 0 ≤ min (f x) ↑n := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
        rw [h] at h1; exact not_le.mpr EReal.bot_lt_zero h1
      have hm_ne_top : min (f x) ↑m ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top m) (min_le_right _ _)
      have hn_ne_top : min (f x) ↑n ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top n) (min_le_right _ _)
      have hm_nonneg : 0 ≤ (min (f x) ↑m).toReal := by
        have h1 : 0 ≤ min (f x) ↑m := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg m))
        exact EReal.toReal_nonneg h1
      have hn_nonneg : 0 ≤ (min (f x) ↑n).toReal := by
        have h1 : 0 ≤ min (f x) ↑n := le_min (hf x) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
        exact EReal.toReal_nonneg h1
      simp only [hm_ne_bot, hm_ne_top, hn_ne_bot, hn_ne_top, ite_false]
      simp only [not_lt.mpr hm_nonneg, not_lt.mpr hn_nonneg, ite_false]
      -- Now we need: floor(t_m * 2^m) / 2^m ≤ floor(t_n * 2^n) / 2^n
      -- Key: t_m ≤ t_n and floor approximation from below
      set t_m := (min (f x) ↑m).toReal with ht_m
      set t_n := (min (f x) ↑n).toReal with ht_n
      have h_tm_le_tn : t_m ≤ t_n := by
        have h1 : min (f x) ↑m ≤ min (f x) ↑n := by
          apply min_le_min_left
          exact EReal.coe_le_coe_iff.mpr (Nat.cast_le.mpr hmn)
        exact EReal.toReal_le_toReal h1 hm_ne_bot hn_ne_top
      have h2m_pos : (0 : ℝ) < 2^m := pow_pos (by norm_num) m
      have h2n_pos : (0 : ℝ) < 2^n := pow_pos (by norm_num) n
      -- floor(t_m * 2^m) / 2^m ≤ t_m ≤ t_n
      have h_floor_le_tm : (⌊t_m * 2^m⌋₊ : ℝ) / 2^m ≤ t_m := by
        have h1 : (⌊t_m * 2^m⌋₊ : ℝ) ≤ t_m * 2^m := Nat.floor_le (mul_nonneg hm_nonneg (le_of_lt h2m_pos))
        rw [div_le_iff₀ h2m_pos]
        linarith
      -- floor(t_n * 2^n) / 2^n is the largest multiple of 2^{-n} ≤ t_n
      -- Since floor(t_m * 2^m) / 2^m is a multiple of 2^{-m}, hence of 2^{-n},
      -- and it's ≤ t_m ≤ t_n, we have the result
      have h_lhs_mul : ∃ k : ℕ, (⌊t_m * 2^m⌋₊ : ℝ) / 2^m = (k : ℝ) / 2^n := by
        use ⌊t_m * 2^m⌋₊ * 2^(n - m)
        have h_pow : (2 : ℝ)^m * 2^(n - m) = 2^n := by
          rw [← pow_add]; congr 1; omega
        field_simp
        ring_nf
        rw [← h_pow]
        push_cast; ring
      obtain ⟨k, hk⟩ := h_lhs_mul
      -- k / 2^n ≤ t_m ≤ t_n, so k / 2^n ≤ floor(t_n * 2^n) / 2^n
      have h_k_le_tn : (k : ℝ) / 2^n ≤ t_n := by
        rw [← hk]; exact le_trans h_floor_le_tm h_tm_le_tn
      have h_k_le_floor : k ≤ ⌊t_n * 2^n⌋₊ := by
        have h1 : (k : ℝ) ≤ t_n * 2^n := by
          rw [div_le_iff₀ h2n_pos] at h_k_le_tn; linarith
        exact Nat.le_floor h1
      -- Final result in ℝ: floor(t_m * 2^m) / 2^m ≤ floor(t_n * 2^n) / 2^n
      have h_real : (⌊t_m * 2^m⌋₊ : ℝ) / 2^m ≤ (⌊t_n * 2^n⌋₊ : ℝ) / 2^n := by
        calc (⌊t_m * 2^m⌋₊ : ℝ) / 2^m = (k : ℝ) / 2^n := hk
             _ ≤ (⌊t_n * 2^n⌋₊ : ℝ) / 2^n := by
               apply div_le_div_of_nonneg_right _ (le_of_lt h2n_pos)
               exact_mod_cast h_k_le_floor
      -- Coerce to EReal
      exact EReal.coe_le_coe_iff.mpr h_real
    · -- |x| > m, so approx_fn f m x = 0
      simp only [hm, ite_false]
      -- approx_fn f n x ≥ 0 by construction (it's unsigned)
      by_cases hn : ‖x‖ ≤ n
      · simp only [hn, ite_true]
        -- Need: 0 ≤ (if bot then 0, if top then n, if neg then 0, else floor/2^n)
        split_ifs with h_bot h_top h_neg
        · exact le_refl 0  -- 0 ≤ 0
        · exact EReal.coe_nonneg.mpr (Nat.cast_nonneg n)  -- 0 ≤ n
        · exact le_refl 0  -- 0 ≤ 0
        · -- 0 ≤ floor(...) / 2^n
          apply EReal.coe_nonneg.mpr
          apply div_nonneg (Nat.cast_nonneg _)
          exact le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) n)
      · simp only [hn, ite_false]
        rfl
  · -- Convergence: f x = iSup (fun n => approx_fn f n x)
    intro x
    -- Case analysis: f x = ⊤ or f x < ⊤
    rcases eq_top_or_lt_top (f x) with hfx_top | hfx_lt_top
    · -- Case 1: f x = ⊤
      rw [hfx_top, eq_comm, iSup_eq_top]
      intro b hb
      -- For b < ⊤, find n with approx_fn f n x > b
      rcases eq_bot_or_bot_lt b with rfl | hb_bot
      · -- b = ⊥: any n works since approx_fn f n x ≥ 0 > ⊥
        use max 1 (Nat.ceil ‖x‖)
        exact lt_of_lt_of_le EReal.bot_lt_zero (approx_fn_nonneg f hf _ x)
      · -- b > ⊥ and b < ⊤, so b is a finite real
        induction b using EReal.rec with
        | bot => exact (not_lt_bot hb_bot).elim
        | top => exact (lt_irrefl _ hb).elim
        | coe b' =>
          -- Choose n > b' and n ≥ ‖x‖
          let N := max (Nat.ceil b' + 1) (Nat.ceil ‖x‖)
          use N
          have h_norm : ‖x‖ ≤ N := by
            calc ‖x‖ ≤ Nat.ceil ‖x‖ := Nat.le_ceil _
                 _ ≤ N := by exact_mod_cast Nat.le_max_right _ _
          -- approx_fn f N x = floor(N * 2^N) / 2^N = N when f x = ⊤
          have hN_ne_bot : ((N : ℕ) : EReal) ≠ ⊥ := EReal.coe_ne_bot N
          have hN_ne_top : ((N : ℕ) : EReal) ≠ ⊤ := EReal.coe_ne_top N
          have hN_nonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
          have hN_toReal : ((N : ℕ) : EReal).toReal = N := EReal.toReal_coe N
          simp only [approx_fn, h_norm, ite_true, hfx_top, min_top_left,
                     hN_ne_bot, hN_ne_top, ite_false, hN_toReal, not_lt.mpr hN_nonneg]
          -- floor(N * 2^N) / 2^N = N
          have h_floor_eq : (⌊(N : ℝ) * 2^N⌋₊ : ℝ) / 2^N = N := by
            have h_nat_mul : (N : ℝ) * (2 : ℝ)^N = ↑(N * 2^N) := by push_cast; ring
            rw [h_nat_mul, Nat.floor_natCast]
            field_simp; push_cast; ring
          simp only [← EReal.coe_div, EReal.coe_lt_coe_iff, h_floor_eq]
          calc b' ≤ Nat.ceil b' := Nat.le_ceil _
               _ < (Nat.ceil b' : ℝ) + 1 := lt_add_one _
               _ ≤ N := by exact_mod_cast Nat.le_max_left _ _
    · -- Case 2: f x < ⊤ (finite)
      have hfx_not_bot : f x ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hf x))
      -- f x is finite: not ⊥ (by unsigned) and not ⊤ (by hypothesis)
      set r := (f x).toReal with hr_def
      have hr_eq : f x = r := (EReal.coe_toReal hfx_lt_top.ne hfx_not_bot).symm
      rw [hr_eq]
      -- f x = r (finite nonnegative real)
      have hr_nonneg : r ≥ 0 := by
        have h := hf x
        rw [hr_eq] at h
        exact EReal.coe_nonneg.mp h
      -- Use floor_approx_iSup_eq: for large n, approx_fn f n x = floor(r * 2^n) / 2^n
      apply le_antisymm
      · -- r ≤ iSup (approx_fn)
        -- Strategy: use floor_approx_iSup_eq and show that for large n, floor_approx ≤ approx_fn
        rw [floor_approx_iSup_eq r hr_nonneg]
        apply iSup_le
        intro n
        -- Find N ≥ n with ‖x‖ ≤ N and r ≤ N
        let N := max n (max (Nat.ceil ‖x‖) (Nat.ceil r))
        have hnN : n ≤ N := Nat.le_max_left _ _
        have h_norm_N : ‖x‖ ≤ N := by
          calc ‖x‖ ≤ Nat.ceil ‖x‖ := Nat.le_ceil _
               _ ≤ max (Nat.ceil ‖x‖) (Nat.ceil r) := by exact_mod_cast le_max_left _ _
               _ ≤ N := by exact_mod_cast le_max_right _ _
        have hrN : r ≤ N := by
          calc r ≤ Nat.ceil r := Nat.le_ceil _
               _ ≤ max (Nat.ceil ‖x‖) (Nat.ceil r) := by exact_mod_cast le_max_right _ _
               _ ≤ N := by exact_mod_cast le_max_right _ _
        -- approx_fn f N x = floor(r * 2^N) / 2^N
        have h_approx_N : approx_fn f N x = (((⌊r * 2^N⌋₊ : ℕ) : ℝ) / (2^N : ℝ) : EReal) :=
          approx_fn_eq_floor_when_finite f hf N x h_norm_N r hr_eq hr_nonneg hrN
        -- floor(r * 2^n) / 2^n ≤ floor(r * 2^N) / 2^N (monotonicity)
        have h2n_pos : (2 : ℝ)^n > 0 := pow_pos (by norm_num) n
        have h2N_pos : (2 : ℝ)^N > 0 := pow_pos (by norm_num) N
        have h_floor_n_le_r : (⌊r * 2^n⌋₊ : ℝ) / 2^n ≤ r := by
          rw [div_le_iff₀ h2n_pos]
          exact Nat.floor_le (mul_nonneg hr_nonneg (le_of_lt h2n_pos))
        have h_mono : (⌊r * 2^n⌋₊ : ℝ) / 2^n ≤ (⌊r * 2^N⌋₊ : ℝ) / 2^N := by
          -- floor(r * 2^n) / 2^n is a multiple of 2^{-n}, hence of 2^{-N}
          have h_lhs_mul : ∃ k : ℕ, (⌊r * 2^n⌋₊ : ℝ) / 2^n = (k : ℝ) / 2^N := by
            use ⌊r * 2^n⌋₊ * 2^(N - n)
            have h_pow : (2 : ℝ)^n * 2^(N - n) = 2^N := by
              rw [← pow_add]; congr 1; omega
            field_simp
            ring_nf
            rw [← h_pow]
            push_cast; ring
          obtain ⟨k, hk⟩ := h_lhs_mul
          rw [hk]
          apply div_le_div_of_nonneg_right _ (le_of_lt h2N_pos)
          have h_k_le_r : (k : ℝ) / 2^N ≤ r := by rw [← hk]; exact h_floor_n_le_r
          have h_k_le_floor : k ≤ ⌊r * 2^N⌋₊ := by
            have h1 : (k : ℝ) ≤ r * 2^N := by
              rw [div_le_iff₀ h2N_pos] at h_k_le_r; linarith
            exact Nat.le_floor h1
          exact_mod_cast h_k_le_floor
        -- Use the monotonicity and connect to iSup
        have h_le_approx : (((⌊r * 2^n⌋₊ : ℕ) : ℝ) / (2^n : ℝ) : EReal) ≤ approx_fn f N x := by
          rw [h_approx_N]
          exact EReal.coe_le_coe_iff.mpr h_mono
        calc (((⌊r * 2^n⌋₊ : ℕ) : ℝ) / (2^n : ℝ) : EReal)
            ≤ approx_fn f N x := h_le_approx
          _ ≤ ⨆ m, approx_fn f m x := le_iSup (fun m => approx_fn f m x) N
      · -- iSup (approx_fn) ≤ r
        apply iSup_le
        intro n
        by_cases h_norm : ‖x‖ ≤ n
        · simp only [approx_fn, h_norm, ite_true, hr_eq]
          -- min r n ≤ r, and floor approx ≤ min r n
          have h_min_ne_bot : min (r : EReal) n ≠ ⊥ := by
            intro h
            rcases min_eq_bot.mp h with hr | hn
            · exact EReal.coe_ne_bot r hr
            · exact EReal.coe_ne_bot n hn
          have h_min_ne_top : min (r : EReal) n ≠ ⊤ :=
            ne_top_of_le_ne_top (EReal.coe_ne_top n) (min_le_right _ _)
          have h_min_nonneg : (min (r : EReal) n).toReal ≥ 0 := by
            apply EReal.toReal_nonneg
            exact le_min (EReal.coe_nonneg.mpr hr_nonneg) (EReal.coe_nonneg.mpr (Nat.cast_nonneg n))
          simp only [h_min_ne_bot, ite_false, h_min_ne_top, not_lt.mpr h_min_nonneg]
          apply EReal.coe_le_coe_iff.mpr
          have h2n_pos : (2 : ℝ)^n > 0 := pow_pos (by norm_num) n
          have h_floor_le : (⌊(min (r : EReal) n).toReal * 2^n⌋₊ : ℝ) / 2^n ≤ (min (r : EReal) n).toReal := by
            rw [div_le_iff₀ h2n_pos]
            exact Nat.floor_le (mul_nonneg h_min_nonneg (le_of_lt h2n_pos))
          have h_min_le_r : (min (r : EReal) n).toReal ≤ r := by
            have h1 : min (r : EReal) n ≤ r := min_le_left _ _
            have h2 := EReal.toReal_le_toReal h1 h_min_ne_bot (EReal.coe_ne_top r)
            simp only [EReal.toReal_coe] at h2
            exact h2
          exact le_trans h_floor_le h_min_le_r
        · simp only [approx_fn, h_norm, ite_false]
          exact EReal.coe_nonneg.mpr hr_nonneg

end UnsignedMeasurable.TFAE_helpers

/-- Lemma 1.3.9 (Equivalent notions of measurability).  Some slight changes to the statement have been made to make the claims cleaner to state -/
theorem UnsignedMeasurable.TFAE {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: Unsigned f):
    [
      UnsignedMeasurable f,
      ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (∀ x, Filter.atTop.Tendsto (fun n ↦ g n x) (nhds (f x))),
      ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n)) ∧ (PointwiseAeConvergesTo g f),
      ∃ (g: ℕ → EuclideanSpace' d → EReal), (∀ n, UnsignedSimpleFunction (g n) ∧  EReal.BoundedFunction (g n) ∧ FiniteMeasureSupport (g n)) ∧ (∀ x, Monotone (fun n ↦ g n x)) ∧ (∀ x, f x = iSup (fun n ↦ g n x)),
      ∀ t, LebesgueMeasurable {x | f x > t},
      ∀ t, LebesgueMeasurable {x | f x ≥ t},
      ∀ t, LebesgueMeasurable {x | f x < t},
      ∀ t, LebesgueMeasurable {x | f x ≤ t},
      ∀ I:BoundedInterval, LebesgueMeasurable (f⁻¹' (Real.toEReal '' I.toSet)),
      ∀ U: Set EReal, IsOpen U → LebesgueMeasurable (f⁻¹' U),
      ∀ K: Set EReal, IsClosed K → LebesgueMeasurable (f⁻¹' K)
    ].TFAE := by
  open UnsignedMeasurable.TFAE_helpers in
  -- Establish the implication graph
  tfae_have 1 ↔ 2 := i_iff_ii hf
  tfae_have 2 → 3 := ii_imp_iii
  tfae_have 4 → 2 := iv_imp_ii
  tfae_have 3 → 5 := iii_imp_v
  tfae_have 5 → 6 := v_imp_vi
  tfae_have 6 → 5 := vi_imp_v
  tfae_have 5 → 8 := v_imp_viii
  tfae_have 6 → 7 := vi_imp_vii
  tfae_have 7 → 6 := vii_imp_vi
  tfae_have 8 → 5 := viii_imp_v
  tfae_have 5 → 9 := fun h => v_to_viii_imp_ix h (v_imp_vi h) (vi_imp_vii (v_imp_vi h)) (v_imp_viii h)
  tfae_have 9 → 10 := ix_imp_x hf
  tfae_have 10 ↔ 11 := x_iff_xi
  tfae_have 10 → 7 := x_imp_vii
  tfae_have 5 → 4 := fun hv => v_to_xi_imp_iv hf (v_imp_vi hv) (vi_imp_vii (v_imp_vi hv))
  tfae_finish

/-- Exercise 1.3.3(i) -/
theorem Continuous.UnsignedMeasurable {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: Continuous f) (hnonneg: Unsigned f): _root_.UnsignedMeasurable f := by
  have h_iff : _root_.UnsignedMeasurable f ↔ ∀ U : Set EReal, IsOpen U → LebesgueMeasurable (f ⁻¹' U) :=
    (_root_.UnsignedMeasurable.TFAE hnonneg).out 1 10
  apply h_iff.mpr
  intro U hU
  exact IsOpen.measurable (hU.preimage hf)

/-- Unsigned simple functions are nonnegative. -/
lemma UnsignedSimpleFunction.unsigned {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) : Unsigned f := by
  intro x
  obtain ⟨k, c, E, hc, heq⟩ := hf
  rw [heq]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_nonneg
  intro i _
  have h1 : 0 ≤ c i := (hc i).2
  have h2 : 0 ≤ EReal.indicator (E i) x := by
    simp only [EReal.indicator, Real.EReal_fun]
    exact EReal.coe_nonneg.mpr (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
  exact mul_nonneg h1 h2

/-- Exercise 1.3.3(ii) -/
theorem UnsignedSimpleFunction.unsignedMeasurable {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f): UnsignedMeasurable f :=
  ⟨hf.unsigned, fun _ ↦ f, fun _ ↦ hf, fun _ ↦ tendsto_const_nhds⟩

/-- Exercise 1.3.3(iii) -/
theorem UnsignedMeasurable.sup {d:ℕ} {f: ℕ → EuclideanSpace' d → EReal} (hf: ∀ n, UnsignedMeasurable (f n)) : UnsignedMeasurable (fun x ↦ iSup (fun n ↦ f n x)) := by
  have hnonneg : Unsigned (fun x ↦ iSup (fun n ↦ f n x)) := by
    intro x
    exact le_trans ((hf 0).1 x) (le_iSup (fun n ↦ f n x) 0)
  have h_iff : UnsignedMeasurable (fun x ↦ iSup (fun n ↦ f n x)) ↔
      ∀ t, LebesgueMeasurable {x | iSup (fun n ↦ f n x) > t} :=
    (UnsignedMeasurable.TFAE hnonneg).out 1 5
  apply h_iff.mpr
  intro t
  have h_eq : {x | iSup (fun n ↦ f n x) > t} = ⋃ n, {x | f n x > t} := by
    ext x
    simp [lt_iSup_iff]
  rw [h_eq]
  refine LebesgueMeasurable.countable_union fun n => ?_
  have hn : UnsignedMeasurable (f n) ↔ ∀ t, LebesgueMeasurable {x | f n x > t} :=
    (UnsignedMeasurable.TFAE (hf n).1).out 1 5
  exact hn.mp (hf n) t

/-- Exercise 1.3.3(iii) -/
theorem UnsignedMeasurable.inf {d:ℕ} {f: ℕ → EuclideanSpace' d → EReal} (hf: ∀ n, UnsignedMeasurable (f n)) : UnsignedMeasurable (fun x ↦ iInf (fun n ↦ f n x)) := by
  have hnonneg : Unsigned (fun x ↦ iInf (fun n ↦ f n x)) := by
    intro x
    exact le_iInf fun n => (hf n).1 x
  have h_iff : UnsignedMeasurable (fun x ↦ iInf (fun n ↦ f n x)) ↔
      ∀ t, LebesgueMeasurable {x | iInf (fun n ↦ f n x) ≥ t} :=
    (UnsignedMeasurable.TFAE hnonneg).out 1 6
  apply h_iff.mpr
  intro t
  have h_eq : {x | iInf (fun n ↦ f n x) ≥ t} = ⋂ n, {x | f n x ≥ t} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact le_iInf_iff
  rw [h_eq]
  refine LebesgueMeasurable.countable_inter fun n => ?_
  have hn : UnsignedMeasurable (f n) ↔ ∀ t, LebesgueMeasurable {x | f n x ≥ t} :=
    (UnsignedMeasurable.TFAE (hf n).1).out 1 6
  exact hn.mp (hf n) t

/-- Exercise 1.3.3(iii) -/
theorem UnsignedMeasurable.limsup {d:ℕ} {f: ℕ → EuclideanSpace' d → EReal} (hf: ∀ n, UnsignedMeasurable (f n)) : UnsignedMeasurable (fun x ↦ Filter.atTop.limsup (fun n ↦ f n x) ) := by
  simpa only [Filter.limsup_eq_iInf_iSup_of_nat'] using
    (UnsignedMeasurable.inf fun n => UnsignedMeasurable.sup fun i => hf (i + n))

/-- Exercise 1.3.3(iii) -/
theorem UnsignedMeasurable.liminf {d:ℕ} {f: ℕ → EuclideanSpace' d → EReal} (hf: ∀ n, UnsignedMeasurable (f n)) : UnsignedMeasurable (fun x ↦ Filter.atTop.liminf (fun n ↦ f n x) ) := by
  simpa only [Filter.liminf_eq_iSup_iInf_of_nat'] using
    (UnsignedMeasurable.sup fun n => UnsignedMeasurable.inf fun i => hf (i + n))

/-- Exercise 1.3.3(iv) -/
theorem UnsignedMeasurable.aeEqual {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg : Unsigned g) (heq: AlmostEverywhereEqual f g) : UnsignedMeasurable g := by
  obtain ⟨_, u, hu, huf⟩ := hf
  have h_iff : UnsignedMeasurable g ↔ ∃ u, (∀ n, UnsignedSimpleFunction (u n)) ∧
      PointwiseAeConvergesTo u g := (UnsignedMeasurable.TFAE hg).out 1 3
  refine h_iff.mpr ⟨u, hu, ?_⟩
  exact AlmostAlways.mp heq fun x hx => hx ▸ huf x

/-- Exercise 1.3.3(v) -/
theorem UnsignedMeasurable.aeLimit {d:ℕ} {f: EuclideanSpace' d → EReal} (g: ℕ → EuclideanSpace' d → EReal) (hf: ∀ n, UnsignedMeasurable (g n)) (hfn : Unsigned f) (heq: PointwiseAeConvergesTo g f) : UnsignedMeasurable f := by
  have hlim : UnsignedMeasurable (fun x => Filter.atTop.limsup (fun n => g n x)) :=
    UnsignedMeasurable.limsup hf
  apply hlim.aeEqual hfn
  exact AlmostAlways.mp heq fun x hx => hx.limsup_eq

/-- Exercise 1.3.3(vi) -/
theorem UnsignedMeasurable.comp_cts {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) {φ: EReal → EReal} (hφ: Continuous φ) (hφnn : ∀ x ≥ 0, φ x ≥ 0) : UnsignedMeasurable (φ ∘ f) := by
  have hnonneg : Unsigned (φ ∘ f) := fun x => hφnn (f x) (hf.1 x)
  have h_source : UnsignedMeasurable f ↔ ∀ U, IsOpen U → LebesgueMeasurable (f ⁻¹' U) :=
    (UnsignedMeasurable.TFAE hf.1).out 1 10
  have h_target : UnsignedMeasurable (φ ∘ f) ↔ ∀ U, IsOpen U → LebesgueMeasurable ((φ ∘ f) ⁻¹' U) :=
    (UnsignedMeasurable.TFAE hnonneg).out 1 10
  exact h_target.mpr fun U hU => h_source.mp hf (φ ⁻¹' U) (hU.preimage hφ)

/-- Exercise 1.3.3(vii) -/
theorem UnsignedMeasurable.add {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedMeasurable f) (hg: UnsignedMeasurable g) : UnsignedMeasurable (f + g) := by
  obtain ⟨hfn, u, hu, huf⟩ := hf
  obtain ⟨hgn, v, hv, hvg⟩ := hg
  refine ⟨fun x => add_nonneg (hfn x) (hgn x),
    fun n => u n + v n, fun n => (hu n).add (hv n), ?_⟩
  intro x
  have hfb : f x ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hfn x))
  have hgb : g x ≠ ⊥ := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (hgn x))
  exact (EReal.continuousAt_add (Or.inr hgb) (Or.inl hfb)).tendsto.comp
    ((huf x).prodMk_nhds (hvg x))

