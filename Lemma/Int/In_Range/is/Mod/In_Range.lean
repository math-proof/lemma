import sympy.sets.fancysets
import Lemma.Int.Abs.eq.Neg.of.Lt_0
import Lemma.Int.EqSign_1.of.Gt_0
import Lemma.Int.EqToNat_0.of.Lt_0
import Lemma.Int.LtToNat.is.Lt.of.Ge_0
import Lemma.Int.Sign.eq.Neg1.of.Lt_0
open Int


private def rangeLen (start stop step : ℤ) : ℕ :=
  (((stop - start) * step.sign + |step| - 1) / |step|).toNat


private lemma mem_Range_iff {start stop step x : ℤ} :
    x ∈ Range start stop step ↔
      ∃ k ∈ List.range (rangeLen start stop step), x = start + (k : ℤ) * step := by
  simp [Range, rangeLen, List.mem_map, List.mem_range, eq_comm]


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
  if hneg : d < 0 then
    have hd' : 0 < -d := neg_pos.mpr hneg
    have h' : (start + j) % (-d) = start % (-d) := by
      rw [Int.emod_neg, Int.emod_neg, h]
    have hj := int_mod_eq_zero_of_add_mod_eq (start := start) (j := j) (d := -d) hd' h'
    rwa [Int.emod_neg j d] at hj
  else
    have hpos : 0 < d := lt_of_le_of_ne (not_lt.mp hneg) hd.symm
    exact int_mod_eq_zero_of_add_mod_eq hpos h


private lemma exists_eq_mul_of_mod_eq_zero {j d : ℤ} (_hd : d ≠ 0) (h : j % d = 0) :
    ∃ k, j = k * d := by
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero h
  exact ⟨k, by rw [Int.mul_comm, hk]⟩


private lemma pos_range_len_mem_bounds {a b d : ℤ} {k : ℕ}
    (hd : 0 < d) (hab : a < b)
    (hk : k ∈ List.range (rangeLen a b d)) :
    a ≤ a + (k : ℤ) * d ∧ a + (k : ℤ) * d < b := by
  have hsign := EqSign_1.of.Gt_0 hd
  have habs : |d| = d := abs_of_pos hd
  simp only [rangeLen, hsign, habs, mul_one] at hk
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
    (hk : k ∈ List.range (rangeLen a b d)) :
    b < a + (k : ℤ) * d ∧ a + (k : ℤ) * d ≤ a := by
  have hsign := Sign.eq.Neg1.of.Lt_0 hd
  have habs : |d| = -d := Abs.eq.Neg.of.Lt_0 hd
  simp only [rangeLen, hsign, habs] at hk
  ring_nf at hk
  have hk_lt := List.mem_range.mp hk
  have hd' : 0 < -d := by omega
  set q := ((-1 - b + a - d) / -d) with hq
  have hq_old : (a - b - d - 1) / (-d) = q := by
    simp [q]
    congr 1
    abel
  have hlen_nonneg : 0 ≤ q := by
    have : 0 < a - b := by omega
    rw [← hq_old]
    omega
  have hk_int : (k : ℤ) < q := by
    rw [← Int.toNat_of_nonneg hlen_nonneg]
    exact_mod_cast hk_lt
  have hk_le : (k : ℤ) ≤ q - 1 := by omega
  have hmod : 0 ≤ (a - b - d - 1) % (-d) := Int.emod_nonneg (a - b - d - 1) (ne_of_gt hd')
  have h_upper : (q - 1) * (-d) < a - b := by
    rw [← hq_old]
    have := Int.emod_add_mul_ediv (a - b - d - 1) (-d)
    linarith
  constructor
  · nlinarith [hk_le, h_upper, hd]
  · nlinarith


private lemma pos_range_index_lt
  {a b d k : ℤ}
  (hd : 0 < d) (hab : a < b)
  (hk0 : 0 ≤ k) (hlt : a + k * d < b) :
  k.toNat < rangeLen a b d := by
  have hsign := EqSign_1.of.Gt_0 hd
  have habs : |d| = d := abs_of_pos hd
  simp only [rangeLen, hsign, habs, mul_one]
  set q := (b - a + d - 1) / d
  have hq_nonneg : 0 ≤ q := Int.ediv_nonneg (by omega) (le_of_lt hd)
  have h_emod := Int.emod_add_mul_ediv (b - a + d - 1) d
  have hr_nonneg : 0 ≤ (b - a + d - 1) % d := Int.emod_nonneg (b - a + d - 1) (ne_of_gt hd)
  have hr_lt : (b - a + d - 1) % d < d := Int.emod_lt_of_pos (b - a + d - 1) hd
  have h_upper : (q - 1) * d < b - a := by linarith
  have hk_lt : k < q := by
    have hbd : k * d < b - a := by omega
    by_contra h
    push Not at h
    have hk_ge_mul : k * d ≥ q * d := by gcongr
    have hq_mul : q * d = b - a + d - 1 - (b - a + d - 1) % d := by linarith
    linarith
  exact LtToNat.of.Lt.Ge_0 hk0 (by rwa [Int.toNat_of_nonneg hq_nonneg])


private lemma neg_range_index_lt
  {a b d m : ℤ}
  (hd : d < 0) (hba : b < a)
  (hm0 : 0 ≤ m) (hgt : b < a + m * d) :
  m.toNat < rangeLen a b d := by
  have hsign := Sign.eq.Neg1.of.Lt_0 hd
  have habs : |d| = -d := Abs.eq.Neg.of.Lt_0 hd
  set q := (a - b - d - 1) / (-d)
  let L := -d
  have hd' : 0 < L := by omega
  have hq_nonneg : 0 ≤ q := Int.ediv_nonneg (by omega) (le_of_lt hd')
  have h_emod := Int.emod_add_mul_ediv (a - b - d - 1) L
  have hr_nonneg : 0 ≤ (a - b - d - 1) % L := Int.emod_nonneg (a - b - d - 1) (ne_of_gt hd')
  have hr_lt : (a - b - d - 1) % L < L := Int.emod_lt_of_pos (a - b - d - 1) hd'
  have h_upper : (q - 1) * L < a - b := by linarith
  have hm_lt : m < q := by
    have hbd : m * L < a - b := by
      have h1 : m * d > b - a := by omega
      calc
        m * L = m * (-d) := by ring
        _ = -(m * d) := by ring
        _ < -(b - a) := by omega
        _ = a - b := by ring
    by_contra h
    push Not at h
    have hm_ge_mul : m * L ≥ q * L := by gcongr
    have hq_mul : q * L = a - b - d - 1 - (a - b - d - 1) % L := by linarith
    linarith [hbd, hq_mul, hm_ge_mul, h_upper, hr_nonneg, hr_lt]
  have hq_old : q = (-1 - b + a - d) / -d := by
    simp [q]
    congr 1
    abel
  have hlen : rangeLen a b d = q.toNat := by
    simp only [rangeLen, hsign, habs]
    ring_nf
    simp [q, hq_old]
  exact LtToNat.of.Lt.Ge_0 hm0 (by
    have hcast := (Int.toNat_of_nonneg hq_nonneg).symm
    rw [hlen, ← hcast]
    exact hm_lt)


private lemma mem_Range_one_iff {a b x : ℤ} :
    x ∈ Range a b 1 ↔ a ≤ x ∧ x < b := by
  by_cases hab : a < b
  ·
    have hlen : rangeLen a b 1 = (b - a).toNat := by
      simp only [rangeLen, Int.sign_one, abs_one, mul_one]
      ring_nf
      rw [Int.ediv_one (b - a), ← Int.toNat_of_nonneg (by omega : 0 ≤ b - a)]
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
    have hlen : rangeLen a b 1 = 0 := by
      simp only [rangeLen, Int.sign_one, abs_one, mul_one]
      ring_nf
      by_cases hn : b - a < 0
      · exact EqToNat_0.of.Lt_0 (by omega : (b - a) / 1 < 0)
      · have heq : b - a = 0 := by omega
        rw [heq]
        rfl
    simp only [mem_Range_iff, hlen, List.range_zero, List.not_mem_nil]
    grind


private lemma mem_Range_neg_one_iff {a b x : ℤ} :
    x ∈ Range a b (-1) ↔ b < x ∧ x ≤ a := by
  by_cases hba : b < a
  ·
    have hlen : rangeLen a b (-1) = (a - b).toNat := by
      simp only [rangeLen, Sign.eq.Neg1.of.Lt_0 (by omega : (-1 : ℤ) < 0), abs_neg]
      ring_nf
      rw [Int.ediv_one (-b + a), show -b + a = a - b by abel]
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
    have hlen : rangeLen a b (-1) = 0 := by
      simp only [rangeLen, Sign.eq.Neg1.of.Lt_0 (by omega : (-1 : ℤ) < 0), abs_neg]
      ring_nf
      by_cases hn : a - b < 0
      · exact EqToNat_0.of.Lt_0 (by omega : (-b + a) / 1 < 0)
      · have heq : a - b = 0 := by omega
        have h0 : -b + a = 0 := by linarith [heq]
        rw [h0]
        rfl
    simp only [mem_Range_iff, hlen, List.range_zero, List.not_mem_nil]
    grind


private lemma pos_rangeLen_zero {a b d : ℤ} (hd : 0 < d) (hab : ¬a < b) :
    rangeLen a b d = 0 := by
  have hsign := EqSign_1.of.Gt_0 hd
  have habs : |d| = d := abs_of_pos hd
  simp only [rangeLen, hsign, habs, mul_one]
  have hlt : b - a + d - 1 < d := by omega
  by_cases hn : 0 ≤ b - a + d - 1
  · rw [Int.ediv_eq_zero_of_lt hn hlt, Int.toNat_zero]
  · rw [EqToNat_0.of.Lt_0 (Int.ediv_neg_of_neg_of_pos (by omega) hd)]


private lemma neg_rangeLen_zero {a b d : ℤ} (hd : d < 0) (hba : ¬b < a) :
    rangeLen a b d = 0 := by
  have hsign := Sign.eq.Neg1.of.Lt_0 hd
  have habs : |d| = -d := Abs.eq.Neg.of.Lt_0 hd
  simp only [rangeLen, hsign, habs]
  ring_nf
  have hlt : -1 - b + a - d < -d := by omega
  by_cases hn : 0 ≤ -1 - b + a - d
  · rw [Int.ediv_eq_zero_of_lt hn hlt, Int.toNat_zero]
  · rw [EqToNat_0.of.Lt_0 (Int.ediv_neg_of_neg_of_pos (by omega) (by omega : 0 < -d))]


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
  · simp only [hd0, Range, Int.sign_zero, abs_zero, Int.ediv_zero, Int.toNat_zero,
      List.range_zero, List.mem_map, Int.emod_zero]
    constructor
    · rintro ⟨_, hk, _⟩
      simp at hk
    · rintro ⟨hx, ⟨_, hk, _⟩⟩
      simp at hk
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
          · simp [pos_rangeLen_zero hpos hab] at hk
      ·
        rintro ⟨hmod, ⟨hle, hlt⟩⟩
        by_cases hab : a < b
        ·
          have hj_mod : (x - a) % d = 0 :=
            int_mod_eq_zero_of_add_mod_eq_any hd0 (by
              calc (a + (x - a)) % d = x % d := by congr 1; ring
              _ = a % d := hmod)
          obtain ⟨k, hk⟩ := exists_eq_mul_of_mod_eq_zero hd0 hj_mod
          have hk0 : 0 ≤ k := by
            have hxa : 0 ≤ x - a := by omega
            rw [hk] at hxa
            nlinarith [hpos]
          refine ⟨k.toNat, ?_, ?_⟩
          ·
            rw [List.mem_range]
            exact pos_range_index_lt hpos hab hk0 (by rw [← hk]; omega)
          ·
            show x = a + (k.toNat : ℤ) * d
            calc
              x = a + (x - a) := by ring
              _ = a + k * d := by rw [← hk]
              _ = a + (k.toNat : ℤ) * d := (Int.toNat_of_nonneg hk0).symm ▸ rfl
        · omega
    ·
      have hneg : d < 0 := by omega
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
          · simp [neg_rangeLen_zero hneg hba] at hk
      ·
        rintro ⟨hmod, ⟨hgt, hle⟩⟩
        by_cases hba : b < a
        ·
          have hj_mod : (a - x) % d = 0 :=
            int_mod_eq_zero_of_add_mod_eq_any hd0 (by
              calc (x + (a - x)) % d = a % d := by congr 1; ring
              _ = x % d := hmod.symm)
          obtain ⟨k, hk⟩ := exists_eq_mul_of_mod_eq_zero hd0 hj_mod
          have hk_nonpos : k ≤ 0 := by
            have hxa : 0 ≤ a - x := by omega
            rw [hk] at hxa
            nlinarith [hneg]
          refine ⟨(-k).toNat, ?_, ?_⟩
          ·
            rw [List.mem_range]
            apply neg_range_index_lt hneg hba (by linarith)
            calc
              b < x := hgt
              _ = a - k * d := by grind
              _ = a + (-k) * d := by ring
          ·
            calc
              x = a - (a - x) := by ring
              _ = a - k * d := by rw [hk]
              _ = a + (-k) * d := by ring
              _ = a + ((-k).toNat : ℤ) * d := by rw [Int.toNat_of_nonneg (by linarith : 0 ≤ -k)]
        · omega


-- created on 2023-05-30
