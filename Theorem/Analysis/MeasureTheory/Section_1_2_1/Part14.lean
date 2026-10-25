import Def.Analysis.MeasureTheory.Section_1_2_0.Part2
import Theorem.Analysis.Misc.RealERealENNReal
import Theorem.Analysis.Misc.Combinatorics
import Def.Analysis.MeasureTheory.Section_1_2_1.Part12
open BoundedInterval

/-!
# Introduction to Measure Theory, Section 1.2.1: Properties of Lebesgue outer measure

A companion to (the introduction to) Section 1.2.1 of the book "An introduction to Measure Theory".

-/


/-- Dyadic boxes have all sides as closed intervals ({name}`BoundedInterval.Icc`). -/
lemma Box.IsDyadic.all_sides_Icc {d : ℕ} {B : Box d} (hB : B.IsDyadic) :
    ∀ i, ∃ a b, B.side i = BoundedInterval.Icc a b := by
  obtain ⟨n, ⟨a, rfl⟩⟩ := hB
  intro i
  use a i / 2^n, (a i + 1) / 2^n
  rfl

-- Helper lemmas for Lemma 1.2.11

namespace DyadicCube

/-- The sidelength of a dyadic cube at scale n is 2^(-n). -/
lemma sidelength {d:ℕ} (n:ℤ) (a: Fin d → ℤ) (i : Fin d) :
    |(DyadicCube n a).side i|ₗ = (2:ℝ)^(-n) := by
  simp only [DyadicCube, BoundedInterval.length, BoundedInterval.b, BoundedInterval.a]
  have h : (↑(a i) + 1) / (2:ℝ) ^ n - ↑(a i) / (2:ℝ) ^ n = (2:ℝ) ^ (-n) := by
    simp only [zpow_neg, ← sub_div]; norm_cast; simp [add_sub_cancel_left]
  rw [h, max_eq_left (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-n))]

/-- Dyadic cubes at scale n ≥ 0 have sidelength at most 1. -/
lemma sidelength_le_one {d:ℕ} {n:ℕ} (a: Fin d → ℤ) (i : Fin d) :
    |(DyadicCube (n:ℤ) a).side i|ₗ ≤ 1 := by
  rw [DyadicCube.sidelength]
  have h1 : (1:ℝ) ≤ 2^n := by
    calc (1:ℝ) = 2^(0:ℕ) := by norm_num
      _ ≤ 2^n := pow_le_pow_right₀ (by norm_num : 1 ≤ (2:ℝ)) (Nat.zero_le n)
  calc (2:ℝ)^(-(n:ℤ)) = 1 / 2^n := by rw [zpow_neg, zpow_natCast]; ring
    _ ≤ 1 / 1 := by apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) h1
    _ = 1 := by norm_num

/-- The interior of a dyadic cube. -/
lemma interior {d:ℕ} (n:ℤ) (a: Fin d → ℤ) :
    interior (DyadicCube n a).toSet =
    {x | ∀ i, x i ∈ Set.Ioo ((a i : ℝ) / 2^n) (((a i : ℝ) + 1) / 2^n)} := by
  rw [Box.interior_toSet]
  ext x; simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_setOf_eq, DyadicCube, BoundedInterval.toSet, interior_Icc]; rfl

/-- Dyadic cubes at the same scale with different indices have disjoint interiors. -/
lemma almost_disjoint_same_scale {d:ℕ} {n:ℤ} {a b : Fin d → ℤ} (hab : a ≠ b) :
    AlmostDisjoint (DyadicCube n a) (DyadicCube n b) := by
  simp only [AlmostDisjoint]
  rw [DyadicCube.interior, DyadicCube.interior]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro ha hb
  apply hab
  funext i
  have hai : x i ∈ Set.Ioo ((a i : ℝ) / 2^n) (((a i : ℝ) + 1) / 2^n) := ha i
  have hbi : x i ∈ Set.Ioo ((b i : ℝ) / 2^n) (((b i : ℝ) + 1) / 2^n) := hb i
  rw [Set.mem_Ioo] at hai hbi
  -- Both intervals contain x i, so a i = b i
  have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num : (0:ℝ) < 2) n
  have ha_floor : ⌊x i * 2^n⌋ = a i := by
    apply Int.floor_eq_iff.mpr
    constructor
    · calc (a i : ℝ) = (a i : ℝ) / 2^n * 2^n := by field_simp
        _ ≤ x i * 2^n := by nlinarith [hai.1]
    · calc x i * 2^n < ((a i : ℝ) + 1) / 2^n * 2^n := by nlinarith [hai.2]
        _ = (a i : ℝ) + 1 := by field_simp
  have hb_floor : ⌊x i * 2^n⌋ = b i := by
    apply Int.floor_eq_iff.mpr
    constructor
    · calc (b i : ℝ) = (b i : ℝ) / 2^n * 2^n := by field_simp
        _ ≤ x i * 2^n := by nlinarith [hbi.1]
    · calc x i * 2^n < ((b i : ℝ) + 1) / 2^n * 2^n := by nlinarith [hbi.2]
        _ = (b i : ℝ) + 1 := by field_simp
  exact ha_floor.symm.trans hb_floor

/-- The dyadic cubes at scale n cover all of ℝᵈ. -/
lemma cover_univ {d:ℕ} (n:ℤ) :
    (⋃ (a : Fin d → ℤ), (DyadicCube n a).toSet) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  use fun i => ⌊x i * 2^n⌋
  intro i
  simp only [DyadicCube, BoundedInterval.toSet, Set.mem_Icc]
  have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num : (0:ℝ) < 2) n
  constructor
  · have h1 : (⌊x i * 2^n⌋ : ℝ) ≤ x i * 2^n := Int.floor_le _
    calc (⌊x i * 2^n⌋ : ℝ) / 2^n ≤ x i * 2^n / 2^n :=
        div_le_div_of_nonneg_right h1 h2n_pos.le
      _ = x i := by field_simp
  · have h2 : x i * 2^n < ⌊x i * 2^n⌋ + 1 := Int.lt_floor_add_one _
    have hle : x i < ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n := by
      calc x i = x i * 2^n / 2^n := by field_simp
        _ < (⌊x i * 2^n⌋ + 1) / 2^n := div_lt_div_of_pos_right h2 h2n_pos
        _ = ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n := by ring
    exact hle.le

/-- Dyadic cubes at the same scale are pairwise almost disjoint. -/
lemma pairwise_almost_disjoint {d:ℕ} (n:ℤ) :
    Pairwise (Function.onFun AlmostDisjoint (DyadicCube n : (Fin d → ℤ) → Box d)) := by
  intro a b hab
  simp only [Function.onFun]
  exact DyadicCube.almost_disjoint_same_scale hab

/-- Two dyadic cubes are either almost disjoint or one contains the other. -/
lemma nesting {d:ℕ} {n m : ℤ} {a : Fin d → ℤ} {b : Fin d → ℤ} :
    AlmostDisjoint (DyadicCube n a) (DyadicCube m b) ∨
    (DyadicCube n a).toSet ⊆ (DyadicCube m b).toSet ∨
    (DyadicCube m b).toSet ⊆ (DyadicCube n a).toSet := by
  -- Case analysis on the relationship between n and m
  rcases lt_trichotomy n m with hn | rfl | hm
  · -- n < m: The cube at scale m has smaller cells (2^(-m) < 2^(-n))
    -- Either DyadicCube m b ⊆ DyadicCube n a (if b is in the right position) or almost disjoint
    -- Check if DyadicCube m b ⊆ DyadicCube n a by checking containment of intervals
    by_cases h_subset : ∀ i, (a i : ℝ) / 2^n ≤ (b i : ℝ) / 2^m ∧ ((b i : ℝ) + 1) / 2^m ≤ ((a i : ℝ) + 1) / 2^n
    · -- DyadicCube m b ⊆ DyadicCube n a
      right; right
      intro x hx i
      simp only [DyadicCube, BoundedInterval.toSet, Set.mem_Icc] at hx ⊢
      have hxi := hx i
      exact ⟨le_trans (h_subset i).1 hxi.1, le_trans hxi.2 (h_subset i).2⟩
    · -- Not contained, so they are almost disjoint
      left
      push_neg at h_subset
      obtain ⟨i, hi⟩ := h_subset
      simp only [AlmostDisjoint, DyadicCube.interior]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro ha hb
      have hai := ha i
      have hbi := hb i
      have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num : (0:ℝ) < 2) n
      have h2m_pos : (0:ℝ) < 2^m := zpow_pos (by norm_num : (0:ℝ) < 2) m
      have h_mn_pos : 0 < m - n := Int.sub_pos_of_lt hn
      have h_zpow_eq : (2:ℝ)^(m-n) * 2^n = 2^m := by
        rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
        congr 1
        omega
      -- hi says: if a_i/2^n ≤ b_i/2^m then (a_i+1)/2^n < (b_i+1)/2^m
      -- Case 1: a_i/2^n > b_i/2^m (the hypothesis of hi fails)
      -- Case 2: a_i/2^n ≤ b_i/2^m but (a_i+1)/2^n < (b_i+1)/2^m (hi applies)
      by_cases h_left : (b i : ℝ) / 2^m < (a i : ℝ) / 2^n
      · -- b_i/2^m < a_i/2^n: left endpoint of b is before left endpoint of a
        by_cases h_disj : ((b i : ℝ) + 1) / 2^m ≤ (a i : ℝ) / 2^n
        · -- Intervals (b_i/2^m, (b_i+1)/2^m) and (a_i/2^n, (a_i+1)/2^n) don't overlap
          linarith [hai.1, hbi.2]
        · -- Intervals overlap: b_i/2^m < a_i/2^n < (b_i+1)/2^m
          push_neg at h_disj
          -- a_i * 2^(m-n) lies strictly between b_i and b_i+1
          -- But a_i * 2^(m-n) is an integer (since m > n implies m-n > 0)
          have hlo : (b i : ℝ) < (a i : ℝ) * 2^(m-n) := by
            have h1 : (b i : ℝ) / 2^m * 2^m < (a i : ℝ) / 2^n * 2^m := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2m_pos)] at h1
            calc (b i : ℝ) < (a i : ℝ) / 2^n * 2^m := h1
              _ = (a i : ℝ) * (2^m / 2^n) := by ring
              _ = (a i : ℝ) * 2^(m-n) := by rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
          have hhi : (a i : ℝ) * 2^(m-n) < (b i : ℝ) + 1 := by
            have h1 : (a i : ℝ) / 2^n * 2^m < ((b i : ℝ) + 1) / 2^m * 2^m := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2m_pos)] at h1
            calc (a i : ℝ) * 2^(m-n) = (a i : ℝ) * (2^m / 2^n) := by
                    rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
              _ = (a i : ℝ) / 2^n * 2^m := by ring
              _ < (b i : ℝ) + 1 := h1
          -- a_i * 2^(m-n) is an integer in (b_i, b_i+1), contradiction
          have h_int : ∃ k : ℤ, (a i : ℝ) * 2^(m-n) = k := by
            have h_pos_exp : ∃ p : ℕ, m - n = p ∧ 0 < p := ⟨(m-n).toNat, (Int.toNat_of_nonneg (le_of_lt h_mn_pos)).symm, by omega⟩
            obtain ⟨p, hp, _⟩ := h_pos_exp
            use a i * 2^p
            simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
            congr 1
            rw [hp, zpow_natCast]
          obtain ⟨k, hk⟩ := h_int
          rw [hk] at hlo hhi
          have : (b i : ℤ) < k ∧ k < b i + 1 := ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
          omega
      · -- ¬(b_i/2^m < a_i/2^n), so a_i/2^n ≤ b_i/2^m
        push_neg at h_left
        -- By hi: (a_i+1)/2^n < (b_i+1)/2^m
        have h_right := hi h_left
        by_cases h_disj : ((a i : ℝ) + 1) / 2^n ≤ (b i : ℝ) / 2^m
        · -- Intervals don't overlap
          linarith [hai.2, hbi.1]
        · -- Intervals overlap: b_i/2^m < (a_i+1)/2^n < (b_i+1)/2^m
          push_neg at h_disj
          -- (a_i+1) * 2^(m-n) lies strictly between b_i and b_i+1
          have hlo : (b i : ℝ) < ((a i : ℝ) + 1) * 2^(m-n) := by
            have h1 : (b i : ℝ) / 2^m * 2^m < ((a i : ℝ) + 1) / 2^n * 2^m := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2m_pos)] at h1
            calc (b i : ℝ) < ((a i : ℝ) + 1) / 2^n * 2^m := h1
              _ = ((a i : ℝ) + 1) * (2^m / 2^n) := by ring
              _ = ((a i : ℝ) + 1) * 2^(m-n) := by rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
          have hhi : ((a i : ℝ) + 1) * 2^(m-n) < (b i : ℝ) + 1 := by
            have h1 : ((a i : ℝ) + 1) / 2^n * 2^m < ((b i : ℝ) + 1) / 2^m * 2^m := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2m_pos)] at h1
            calc ((a i : ℝ) + 1) * 2^(m-n) = ((a i : ℝ) + 1) * (2^m / 2^n) := by
                    rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
              _ = ((a i : ℝ) + 1) / 2^n * 2^m := by ring
              _ < (b i : ℝ) + 1 := h1
          -- (a_i+1) * 2^(m-n) is an integer in (b_i, b_i+1), contradiction
          have h_int : ∃ k : ℤ, ((a i : ℝ) + 1) * 2^(m-n) = k := by
            have h_pos_exp : ∃ p : ℕ, m - n = p ∧ 0 < p := ⟨(m-n).toNat, (Int.toNat_of_nonneg (le_of_lt h_mn_pos)).symm, by omega⟩
            obtain ⟨p, hp, _⟩ := h_pos_exp
            use (a i + 1) * 2^p
            simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_add, Int.cast_one]
            congr 1
            rw [hp, zpow_natCast]
          obtain ⟨k, hk⟩ := h_int
          rw [hk] at hlo hhi
          have : (b i : ℤ) < k ∧ k < b i + 1 := ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
          omega
  · -- n = m: Same scale, use almost_disjoint_same_scale or equality
    by_cases hab : a = b
    · subst hab
      right; left
      exact Set.Subset.refl _
    · left
      exact DyadicCube.almost_disjoint_same_scale hab
  · -- m < n: The cube at scale n has smaller cells (2^(-n) < 2^(-m))
    -- Either DyadicCube n a ⊆ DyadicCube m b (if a is in the right position) or almost disjoint
    by_cases h_subset : ∀ i, (b i : ℝ) / 2^m ≤ (a i : ℝ) / 2^n ∧ ((a i : ℝ) + 1) / 2^n ≤ ((b i : ℝ) + 1) / 2^m
    · -- DyadicCube n a ⊆ DyadicCube m b
      right; left
      intro x hx i
      simp only [DyadicCube, BoundedInterval.toSet, Set.mem_Icc] at hx ⊢
      have hxi := hx i
      exact ⟨le_trans (h_subset i).1 hxi.1, le_trans hxi.2 (h_subset i).2⟩
    · -- Not contained, so they are almost disjoint
      left
      push_neg at h_subset
      obtain ⟨i, hi⟩ := h_subset
      simp only [AlmostDisjoint, DyadicCube.interior]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro ha hb
      have hai := ha i
      have hbi := hb i
      have h2n_pos : (0:ℝ) < 2^n := zpow_pos (by norm_num : (0:ℝ) < 2) n
      have h2m_pos : (0:ℝ) < 2^m := zpow_pos (by norm_num : (0:ℝ) < 2) m
      have h_nm_pos : 0 < n - m := Int.sub_pos_of_lt hm
      -- hi says: if b_i/2^m ≤ a_i/2^n then (a_i+1)/2^n > (b_i+1)/2^m
      by_cases h_left : (a i : ℝ) / 2^n < (b i : ℝ) / 2^m
      · -- a_i/2^n < b_i/2^m: left endpoint of a is before left endpoint of b
        by_cases h_disj : ((a i : ℝ) + 1) / 2^n ≤ (b i : ℝ) / 2^m
        · -- Intervals don't overlap
          linarith [hai.2, hbi.1]
        · -- Intervals overlap: a_i/2^n < b_i/2^m < (a_i+1)/2^n
          push_neg at h_disj
          -- b_i * 2^(n-m) lies strictly between a_i and a_i+1
          have hlo : (a i : ℝ) < (b i : ℝ) * 2^(n-m) := by
            have h1 : (a i : ℝ) / 2^n * 2^n < (b i : ℝ) / 2^m * 2^n := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2n_pos)] at h1
            calc (a i : ℝ) < (b i : ℝ) / 2^m * 2^n := h1
              _ = (b i : ℝ) * (2^n / 2^m) := by ring
              _ = (b i : ℝ) * 2^(n-m) := by rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
          have hhi : (b i : ℝ) * 2^(n-m) < (a i : ℝ) + 1 := by
            have h1 : (b i : ℝ) / 2^m * 2^n < ((a i : ℝ) + 1) / 2^n * 2^n := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2n_pos)] at h1
            calc (b i : ℝ) * 2^(n-m) = (b i : ℝ) * (2^n / 2^m) := by
                    rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
              _ = (b i : ℝ) / 2^m * 2^n := by ring
              _ < (a i : ℝ) + 1 := h1
          -- b_i * 2^(n-m) is an integer in (a_i, a_i+1), contradiction
          have h_int : ∃ k : ℤ, (b i : ℝ) * 2^(n-m) = k := by
            have h_pos_exp : ∃ p : ℕ, n - m = p ∧ 0 < p := ⟨(n-m).toNat, (Int.toNat_of_nonneg (le_of_lt h_nm_pos)).symm, by omega⟩
            obtain ⟨p, hp, _⟩ := h_pos_exp
            use b i * 2^p
            simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
            congr 1
            rw [hp, zpow_natCast]
          obtain ⟨k, hk⟩ := h_int
          rw [hk] at hlo hhi
          have : (a i : ℤ) < k ∧ k < a i + 1 := ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
          omega
      · -- ¬(a_i/2^n < b_i/2^m), so b_i/2^m ≤ a_i/2^n
        push_neg at h_left
        -- By hi: (a_i+1)/2^n > (b_i+1)/2^m
        have h_right := hi h_left
        by_cases h_disj : ((b i : ℝ) + 1) / 2^m ≤ (a i : ℝ) / 2^n
        · -- Intervals don't overlap
          linarith [hai.1, hbi.2]
        · -- Intervals overlap: a_i/2^n < (b_i+1)/2^m < (a_i+1)/2^n
          push_neg at h_disj
          -- (b_i+1) * 2^(n-m) lies strictly between a_i and a_i+1
          have hlo : (a i : ℝ) < ((b i : ℝ) + 1) * 2^(n-m) := by
            have h1 : (a i : ℝ) / 2^n * 2^n < ((b i : ℝ) + 1) / 2^m * 2^n := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2n_pos)] at h1
            calc (a i : ℝ) < ((b i : ℝ) + 1) / 2^m * 2^n := h1
              _ = ((b i : ℝ) + 1) * (2^n / 2^m) := by ring
              _ = ((b i : ℝ) + 1) * 2^(n-m) := by rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
          have hhi : ((b i : ℝ) + 1) * 2^(n-m) < (a i : ℝ) + 1 := by
            have h1 : ((b i : ℝ) + 1) / 2^m * 2^n < ((a i : ℝ) + 1) / 2^n * 2^n := by nlinarith
            simp only [div_mul_cancel₀ _ (ne_of_gt h2n_pos)] at h1
            calc ((b i : ℝ) + 1) * 2^(n-m) = ((b i : ℝ) + 1) * (2^n / 2^m) := by
                    rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0)]
              _ = ((b i : ℝ) + 1) / 2^m * 2^n := by ring
              _ < (a i : ℝ) + 1 := h1
          -- (b_i+1) * 2^(n-m) is an integer in (a_i, a_i+1), contradiction
          have h_int : ∃ k : ℤ, ((b i : ℝ) + 1) * 2^(n-m) = k := by
            have h_pos_exp : ∃ p : ℕ, n - m = p ∧ 0 < p := ⟨(n-m).toNat, (Int.toNat_of_nonneg (le_of_lt h_nm_pos)).symm, by omega⟩
            obtain ⟨p, hp, _⟩ := h_pos_exp
            use (b i + 1) * 2^p
            simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_add, Int.cast_one]
            congr 1
            rw [hp, zpow_natCast]
          obtain ⟨k, hk⟩ := h_int
          rw [hk] at hlo hhi
          have : (a i : ℤ) < k ∧ k < a i + 1 := ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
          omega

end DyadicCube

/-- For any point x in an open set E, there exists a dyadic cube containing x with the cube contained in E. -/
lemma IsOpen.exists_dyadic_cube_subset {d:ℕ} {E : Set (EuclideanSpace' d)} (hE : IsOpen E)
    {x : EuclideanSpace' d} (hx : x ∈ E) :
    ∃ n : ℕ, ∃ a : Fin d → ℤ, x ∈ (DyadicCube (n:ℤ) a).toSet ∧
    (DyadicCube (n:ℤ) a).toSet ⊆ E := by
  -- Since E is open, there exists ε > 0 such that B(x, ε) ⊆ E
  rw [Metric.isOpen_iff] at hE
  obtain ⟨ε, hε_pos, hball⟩ := hE x hx
  -- Choose n large enough that the dyadic cube containing x has diameter < ε
  -- Diameter of dyadic cube at scale n is ≤ √d * 2^(-n)
  -- We need √d * 2^(-n) < ε, i.e., √d / ε < 2^n
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Real.sqrt d / ε) (by norm_num : (1:ℝ) < 2)
  use n
  -- Find the dyadic cube containing x at scale n
  let a : Fin d → ℤ := fun i => ⌊x i * 2^n⌋
  use a
  have h2n_pos : (0:ℝ) < 2^n := by positivity
  constructor
  · -- x ∈ DyadicCube n a
    intro i
    simp only [DyadicCube, BoundedInterval.toSet, Set.mem_Icc]
    constructor
    · have h1 : (⌊x i * 2^n⌋ : ℝ) ≤ x i * 2^n := Int.floor_le _
      have h2 := div_le_div_of_nonneg_right h1 (le_of_lt h2n_pos)
      simp only [mul_div_cancel_right₀ _ (ne_of_gt h2n_pos)] at h2
      exact h2
    · have h2 : x i * 2^n < ⌊x i * 2^n⌋ + 1 := Int.lt_floor_add_one _
      have h3 := div_lt_div_of_pos_right h2 h2n_pos
      simp only [mul_div_cancel_right₀ _ (ne_of_gt h2n_pos)] at h3
      exact h3.le
  · -- DyadicCube n a ⊆ E
    intro y hy
    apply hball
    simp only [Metric.mem_ball]
    -- y is in the dyadic cube containing x, so |y i - x i| ≤ 2^(-n) for all i
    have h2n_inv : (2:ℝ)^(-n:ℤ) = 1 / 2^n := by rw [zpow_neg, zpow_natCast]; ring
    have h_zpow : (2:ℝ) ^ (↑n:ℤ) = 2 ^ n := zpow_natCast 2 n
    have hyi : ∀ i, |y i - x i| ≤ 2^(-n:ℤ) := fun i => by
      have hyi_mem := hy i
      simp only [DyadicCube, BoundedInterval.toSet, Set.mem_Icc, h_zpow] at hyi_mem
      -- hyi_mem : ⌊x i * 2^n⌋ / 2^n ≤ y i ∧ y i ≤ (⌊x i * 2^n⌋ + 1) / 2^n
      have hxi_floor : (⌊x i * 2^n⌋ : ℝ) / 2^n ≤ x i := by
        have h1 := Int.floor_le (x i * 2^n)
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt h2n_pos)
        simp only [mul_div_cancel_right₀ _ (ne_of_gt h2n_pos)] at h2
        exact h2
      rw [abs_le, h2n_inv]
      -- We need: -1/2^n ≤ y i - x i ≤ 1/2^n
      have hbound : x i - 1 / 2^n ≤ (⌊x i * 2^n⌋ : ℝ) / 2^n := by
        have h1 := (Int.lt_floor_add_one (x i * 2^n)).le
        have h2 := div_le_div_of_nonneg_right h1 (le_of_lt h2n_pos)
        simp only [mul_div_cancel_right₀ _ (ne_of_gt h2n_pos)] at h2
        have heq : ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n = (⌊x i * 2^n⌋ : ℝ) / 2^n + 1 / 2^n := by ring
        linarith [heq, h2]
      have hwidth : ((⌊x i * 2^n⌋ : ℝ) + 1) / 2^n - (⌊x i * 2^n⌋ : ℝ) / 2^n = 1 / 2^n := by ring
      -- Lower bound: floor/2^n ≤ y i and x i - 1/2^n ≤ floor/2^n, so x i - 1/2^n ≤ y i
      refine ⟨?_, ?_⟩
      · linarith [hyi_mem.1, hbound]
      · -- Upper bound: y i ≤ (floor+1)/2^n and floor/2^n ≤ x i
        -- So y i - x i ≤ (floor+1)/2^n - floor/2^n = 1/2^n
        linarith [hyi_mem.2, hxi_floor, hwidth]
    -- dist y x ≤ √d * 2^(-n) < ε
    have hdist : dist y x ≤ Real.sqrt d * (2:ℝ)^(-n:ℤ) := by
      rw [EuclideanSpace.dist_eq]
      have hdist_eq : ∀ i, dist (y i) (x i) = |y i - x i| := fun i => Real.dist_eq (y i) (x i)
      simp_rw [hdist_eq]
      have hsqrt_mul : Real.sqrt d * (2:ℝ)^(-n:ℤ) = Real.sqrt (d * ((2:ℝ)^(-n:ℤ))^2) := by
        rw [Real.sqrt_mul (by positivity : (d:ℝ) ≥ 0), Real.sqrt_sq (by positivity)]
      rw [hsqrt_mul]
      apply Real.sqrt_le_sqrt
      calc ∑ i, |y i - x i|^2
          ≤ ∑ _i : Fin d, ((2:ℝ)^(-n:ℤ))^2 := by
            apply Finset.sum_le_sum
            intro i _
            have h := hyi i
            have h2n_nn : (0:ℝ) ≤ (2:ℝ)^(-n:ℤ) := by positivity
            exact sq_le_sq' (by nlinarith [abs_nonneg (y i - x i)]) h
        _ = d * ((2:ℝ)^(-n:ℤ))^2 := by rw [Finset.sum_const, Finset.card_fin]; ring
    calc dist y x ≤ Real.sqrt d * (2:ℝ)^(-n:ℤ) := hdist
      _ = Real.sqrt d / 2^n := by rw [h2n_inv]; ring
      _ < ε := by
          rw [div_lt_iff₀ h2n_pos]
          calc Real.sqrt d = Real.sqrt d / ε * ε := by field_simp
            _ < ε * 2^n := by nlinarith [hn, hε_pos]

