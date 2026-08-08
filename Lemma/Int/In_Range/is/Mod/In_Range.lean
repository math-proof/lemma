import sympy.sets.fancysets
import Lemma.Int.EqSign_1.of.Gt_0
import Lemma.Int.Sign.eq.Neg1.of.Lt_0
open Int


private lemma mem_Range_iff {start stop step x : ℤ} :
    x ∈ Range start stop step ↔
      ∃ k ∈ List.range (Range.length start stop step), x = start + (k : ℤ) * step := by
  simp [Range, List.mem_map, List.mem_range, eq_comm]


private lemma int_add_mul_emod (m k d : ℤ) : (m + k * d) % d = m % d := by
  simp [Int.add_emod]


private lemma int_mod_eq_zero_of_add_mod_eq
  {start j d : ℤ}
-- given
  (hd : 0 < d)
  (h : (start + j) % d = start % d) :
-- imply
  j % d = 0 := by
-- proof
  set a := start % d
  set b := j % d
  have h' : (a + b) % d = a := by simpa [Int.add_emod, Int.emod_emod, a, b] using h
  have ha : 0 ≤ a ∧ a < d := ⟨Int.emod_nonneg start (ne_of_gt hd), Int.emod_lt_of_pos start hd⟩
  have hb : 0 ≤ b ∧ b < d := ⟨Int.emod_nonneg j (ne_of_gt hd), Int.emod_lt_of_pos j hd⟩
  if hb0 : b = 0 then
    simp [hb0, b]
  else
    have hb_pos : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hb0)
    if hab_lt : a + b < d then
      rw [Int.emod_eq_of_lt (by omega) hab_lt] at h'
      omega
    else
      have hab_ge : d ≤ a + b := by omega
      have hb' : b = d * ((a + b) / d) := by linarith [Int.emod_add_mul_ediv (a + b) d, h']
      have hquot1 : (a + b) / d = 1 := by
        have hlo : 1 ≤ (a + b) / d := by
          rw [Int.le_ediv_iff_mul_le (by omega : (0 : ℤ) < d)]
          omega
        have hhi : (a + b) / d ≤ 1 := by
          have hbound : a + b < 2 * d := by omega
          have : (a + b) / d < 2 :=
            (Int.ediv_lt_iff_lt_mul (by omega : (0 : ℤ) < d)).mpr (by linarith)
          omega
        omega
      have : b = d := by simpa [hquot1] using hb'
      exact absurd this (ne_of_lt hb.2)


private lemma int_mod_eq_zero_of_add_mod_eq_any
  {start j d : ℤ}
-- given
  (hd : d ≠ 0)
  (h : (start + j) % d = start % d) :
-- imply
  j % d = 0 := by
-- proof
  rcases ne_iff_lt_or_gt.mp hd with hneg | hpos
  ·
    have hd' : 0 < -d := neg_pos.mpr hneg
    have h' : (start + j) % (-d) = start % (-d) := by
      rw [Int.emod_neg, Int.emod_neg, h]
    have hj := int_mod_eq_zero_of_add_mod_eq (start := start) (j := j) (d := -d) hd' h'
    rwa [Int.emod_neg j d] at hj
  ·
    exact int_mod_eq_zero_of_add_mod_eq hpos h


private lemma exists_eq_mul_of_mod_eq_zero {j d : ℤ} (_hd : d ≠ 0) (h : j % d = 0) :
    ∃ k, j = k * d := by
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
  exact ⟨k, by rw [Int.mul_comm, hk]⟩


private lemma pos_range_len_mem_bounds {a b d : ℤ} {k : ℕ}
    (hd : 0 < d) (hab : a < b)
    (hk : k ∈ List.range (Range.length a b d)) :
    a ≤ a + (k : ℤ) * d ∧ a + (k : ℤ) * d < b := by
  have hlen : Range.length a b d = ((b - a + d - 1) / d).toNat := by
    unfold Range.length
    simp only [ne_of_gt hd, hd, hab, ite_false, ite_true]
  rw [hlen] at hk
  have hk_lt := List.mem_range.mp hk
  set q := (b - a + d - 1) / d with hq
  have hlen_nonneg : 0 ≤ q := by
    have : 0 < b - a := by omega
    omega
  have hk_int : (k : ℤ) < q := by
    rw [← Int.toNat_of_nonneg hlen_nonneg]
    exact_mod_cast hk_lt
  have hk_le : (k : ℤ) ≤ q - 1 := by omega
  have hmod : 0 ≤ (b - a + d - 1) % d := Int.emod_nonneg (b - a + d - 1) (ne_of_gt hd)
  have h_upper : (q - 1) * d < b - a := by
    have := Int.emod_add_mul_ediv (b - a + d - 1) d
    linarith
  constructor
  · nlinarith
  · nlinarith [hk_le, h_upper, hd]


private lemma neg_range_len_mem_bounds {a b d : ℤ} {k : ℕ}
    (hd : d < 0) (hba : b < a)
    (hk : k ∈ List.range (Range.length a b d)) :
    b < a + (k : ℤ) * d ∧ a + (k : ℤ) * d ≤ a := by
  have hlen : Range.length a b d = ((a - b - d - 1) / (-d)).toNat := by
    unfold Range.length
    simp only [ne_of_lt hd, not_lt.mpr (le_of_lt hd), hba, ite_false, ite_false, ite_true]
  rw [hlen] at hk
  have hk_lt := List.mem_range.mp hk
  have hd' : 0 < -d := by omega
  set q := (a - b - d - 1) / (-d) with hq
  have hlen_nonneg : 0 ≤ q := by
    have : 0 < a - b := by omega
    omega
  have hk_int : (k : ℤ) < q := by
    rw [← Int.toNat_of_nonneg hlen_nonneg]
    exact_mod_cast hk_lt
  have hk_le : (k : ℤ) ≤ q - 1 := by omega
  have hmod : 0 ≤ (a - b - d - 1) % (-d) := Int.emod_nonneg (a - b - d - 1) (ne_of_gt hd')
  have h_upper : (q - 1) * (-d) < a - b := by
    have := Int.emod_add_mul_ediv (a - b - d - 1) (-d)
    linarith
  constructor
  · nlinarith [hk_le, h_upper, hd]
  · nlinarith


private lemma mem_Range_one_iff {a b x : ℤ} :
    x ∈ Range a b 1 ↔ a ≤ x ∧ x < b := by
  by_cases hab : a < b
  ·
    have hlen : Range.length a b 1 = (b - a).toNat := by
      simp [Range.length, hab]
    rw [mem_Range_iff, hlen]
    constructor
    ·
      rintro ⟨k, hk, hx⟩
      rw [hx]
      constructor
      · have := (List.mem_range.mp hk).le
        omega
      · have := List.mem_range.mp hk
        omega
    ·
      rintro ⟨hle, hlt⟩
      refine ⟨(x - a).toNat, List.mem_range.mpr ?_, ?_⟩
      ·
        have hxa : 0 ≤ x - a := by omega
        exact (Int.toNat_lt hxa).mpr (by omega)
      ·
        have hxa : 0 ≤ x - a := by omega
        rw [Int.toNat_of_nonneg hxa]
        ring
  ·
    have hlen : Range.length a b 1 = 0 := by
      simp [Range.length, not_lt.mp hab]
    simp only [mem_Range_iff, hlen, List.range_zero, List.not_mem_nil]
    grind


private lemma mem_Range_neg_one_iff {a b x : ℤ} :
    x ∈ Range a b (-1) ↔ b < x ∧ x ≤ a := by
  by_cases hba : b < a
  ·
    have hlen : Range.length a b (-1) = (a - b).toNat := by
      simp [Range.length, hba]
    rw [mem_Range_iff, hlen]
    constructor
    ·
      rintro ⟨k, hk, hx⟩
      rw [hx]
      constructor
      · have := List.mem_range.mp hk
        omega
      · have := (List.mem_range.mp hk).le
        omega
    ·
      rintro ⟨hgt, hle⟩
      refine ⟨(a - x).toNat, List.mem_range.mpr ?_, ?_⟩
      ·
        have hxa : 0 ≤ a - x := by omega
        exact (Int.toNat_lt hxa).mpr (by omega)
      ·
        have hxa : 0 ≤ a - x := by omega
        rw [Int.toNat_of_nonneg hxa]
        ring
  ·
    have hlen : Range.length a b (-1) = 0 := by
      simp [Range.length, not_lt.mp hba]
    simp only [mem_Range_iff, hlen, List.range_zero, List.not_mem_nil]
    grind


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.In_Range.is.Mod.In_Range |
| comm | Int.Mod.In_Range.is.In_Range |
| mp | Int.Mod.In_Range.of.In_Range |
| mpr | Int.In_Range.of.Mod.In_Range |
-/
@[main, comm, mp, mpr]
private lemma main
  {x a b d : ℤ} :
-- imply
  x ∈ Range a b d ↔ x % d = a % d ∧ x ∈ Range a b (sign d) := by
-- proof
  by_cases hd0 : d = 0
  · simp [hd0, Range, Range.length, sign_zero]
  ·
    by_cases hpos : 0 < d
    ·
      have hsign := EqSign_1.of.Gt_0 hpos
      rw [hsign, mem_Range_iff, mem_Range_one_iff]
      constructor
      ·
        rintro ⟨k, hk, hx⟩
        constructor
        · rw [hx, int_add_mul_emod]
        ·
          rw [hx]
          by_cases hab : a < b
          · exact pos_range_len_mem_bounds hpos hab hk
          · simp only [Range.length, hpos, hab, ite_false] at hk
            simpa [List.range_zero] using hk
      ·
        rintro ⟨hmod, ⟨hle, hlt⟩⟩
        by_cases hab : a < b
        ·
          have hj_mod : (x - a) % d = 0 :=
            int_mod_eq_zero_of_add_mod_eq_any hd0 (by
              calc (a + (x - a)) % d = x % d := by simp [sub_add_cancel]
              _ = a % d := hmod)
          obtain ⟨k, hk⟩ := exists_eq_mul_of_mod_eq_zero hd0 hj_mod
          have hk0 : 0 ≤ k := by
            have hxa : 0 ≤ x - a := by omega
            rw [hk] at hxa
            nlinarith [hpos]
          refine ⟨k.toNat, ?_, ?_⟩
          ·
            simp only [Range.length, show d ≠ 0 from hd0, hpos, hab, ite_false, ite_true, List.mem_range]
            have hbound : k * d ≤ b - a - 1 := by rw [← hk]; omega
            have hk_le : k ≤ (b - a - 1) / d := (Int.le_ediv_iff_mul_le hpos).mpr hbound
            have hlen_nonneg : 0 ≤ (b - a + d - 1) / d := Int.ediv_nonneg (by omega) (le_of_lt hpos)
            have hk_lt' : k < (b - a + d - 1) / d := by
              have hlt_div : (b - a - 1) / d < (b - a + d - 1) / d := by
                apply (Int.ediv_lt_iff_lt_mul hpos).mpr
                have := Int.emod_add_mul_ediv (b - a - 1) d
                linarith
              omega
            have hk_nat_lt : k.toNat < ((b - a + d - 1) / d).toNat := by
              apply (Int.toNat_lt hk0).mpr
              rw [← Int.toNat_of_nonneg hlen_nonneg]
              exact hk_lt'
            exact hk_nat_lt
          ·
            calc
              x = a + (x - a) := by ring
              _ = a + k * d := by rw [hk]
              _ = a + (k.toNat : ℤ) * d := by
                conv_lhs => rw [← Int.toNat_of_nonneg hk0]
        · omega
    ·
      have hneg : d < 0 := lt_of_le_of_ne (not_lt.mp hpos) hd0
      have hsign := Sign.eq.Neg1.of.Lt_0 hneg
      rw [hsign, mem_Range_iff, mem_Range_neg_one_iff]
      constructor
      ·
        rintro ⟨k, hk, hx⟩
        constructor
        · rw [hx, int_add_mul_emod]
        ·
          rw [hx]
          by_cases hba : b < a
          · exact neg_range_len_mem_bounds hneg hba hk
          · simp only [Range.length, hpos, hneg, hba, ite_false, ite_false] at hk
            simpa [List.range_zero] using hk
      ·
        rintro ⟨hmod, ⟨hgt, hle⟩⟩
        by_cases hba : b < a
        ·
          have hj_mod : (a - x) % d = 0 :=
            int_mod_eq_zero_of_add_mod_eq_any hd0 (by
              calc (x + (a - x)) % d = a % d := by simp [Int.add_sub_cancel]
              _ = x % d := hmod.symm)
          obtain ⟨k, hk⟩ := exists_eq_mul_of_mod_eq_zero hd0 hj_mod
          have hk_nonpos : k ≤ 0 := by
            have : a - x ≥ 0 := by omega
            rw [hk] at this
            nlinarith [hneg]
          refine ⟨(-k).toNat, ?_, ?_⟩
          ·
            have hk_nat_eq : (-k) = ((-k).toNat : ℤ) :=
              (Int.toNat_of_nonneg (by linarith : 0 ≤ -k)).symm
            simp only [Range.length, show d ≠ 0 from hd0, hpos, hneg, hba, ite_false, ite_true, List.mem_range]
            have hd' : 0 < -d := by omega
            have hk_le : (-k) ≤ (a - b - 1) / (-d) := by
              apply (Int.le_ediv_iff_mul_le hd').mpr
              calc
                (-k) * (-d) = k * d := by ring
                _ = a - x := hk.symm
                _ ≤ a - b - 1 := by omega
            have hlen_nonneg : 0 ≤ (a - b - d - 1) / (-d) := Int.ediv_nonneg (by omega) (le_of_lt hd')
            have hk_lt' : -k < (a - b - d - 1) / (-d) := by
              have hlt_div : (a - b - 1) / (-d) < (a - b - d - 1) / (-d) := by
                apply (Int.ediv_lt_iff_lt_mul hd').mpr
                have := Int.emod_add_mul_ediv (a - b - 1) (-d)
                linarith
              omega
            have hk_nat_lt : (-k).toNat < ((a - b - d - 1) / (-d)).toNat := by
              apply (Int.toNat_lt (by linarith : 0 ≤ -k)).mpr
              rw [← Int.toNat_of_nonneg hlen_nonneg]
              exact hk_lt'
            exact hk_nat_lt
          ·
            have hk_nat_eq : (-k) = ((-k).toNat : ℤ) :=
              (Int.toNat_of_nonneg (by linarith : 0 ≤ -k)).symm
            calc
              x = a - (a - x) := by ring
              _ = a - k * d := by rw [hk]
              _ = a + (-k) * d := by ring
              _ = a + ((-k).toNat : ℤ) * d := by rw [← hk_nat_eq]
        · omega


-- created on 2023-05-30
