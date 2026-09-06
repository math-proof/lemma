import sympy.sets.fancysets
import Lemma.Int.Abs.eq.Neg.of.Lt_0
import Lemma.Int.Any_Eq_Mul.of.Mod.eq.Zero
import Lemma.Int.EqSign_1.of.Gt_0
import Lemma.Int.EqToNat_0.of.Lt_0
import Lemma.Int.In_Range.is.Any_Eq_AddMul
import Lemma.Int.In_Range.is.Gt.Le
import Lemma.Int.In_Range.is.Le.Lt
import Lemma.Int.LtToNat.is.Lt.of.Ge_0
import Lemma.Int.Mod.eq.Zero.of.ModAdd.eq.Mod.Ne_0
import Lemma.Int.Sign.eq.Neg1.of.Lt_0
open Int


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
      rw [hsign, In_Range.is.Any_Eq_AddMul, In_Range.is.Le.Lt]
      constructor
      ·
        rintro ⟨k, hk, hx⟩
        constructor
        · simp [hx, Int.add_emod]
        ·
          rw [hx]
          by_cases hab : a < b
          ·
            have habs : |d| = d := abs_of_pos hpos
            simp only [hsign, habs, mul_one] at hk
            have hk_lt := List.mem_range.mp hk
            set q := (b - a + d - 1) / d with hq
            have hlen_nonneg : 0 ≤ q := by
              have : 0 < b - a := by omega
              omega
            have hk_int : (k : ℤ) < q := by
              rw [← Int.toNat_of_nonneg hlen_nonneg]
              exact_mod_cast hk_lt
            have hk_le : (k : ℤ) ≤ q - 1 := by omega
            have hmod : 0 ≤ (b - a + d - 1) % d := Int.emod_nonneg (b - a + d - 1) (ne_of_gt hpos)
            have h_upper : (q - 1) * d < b - a := by
              have := Int.emod_add_mul_ediv (b - a + d - 1) d
              linarith
            constructor
            · nlinarith
            · nlinarith [hk_le, h_upper, hpos]
          ·
            have hlen : (((b - a) * d.sign + |d| - 1) / |d|).toNat = 0 := by
              have habs : |d| = d := abs_of_pos hpos
              simp only [hsign, habs, mul_one]
              have hlt : b - a + d - 1 < d := by omega
              by_cases hn : 0 ≤ b - a + d - 1
              · rw [Int.ediv_eq_zero_of_lt hn hlt, Int.toNat_zero]
              · rw [EqToNat_0.of.Lt_0 (Int.ediv_neg_of_neg_of_pos (by omega) hpos)]
            simp [hlen] at hk
      ·
        rintro ⟨hmod, ⟨hle, hlt⟩⟩
        by_cases hab : a < b
        ·
          have hj_mod : (x - a) % d = 0 :=
            Mod.eq.Zero.of.ModAdd.eq.Mod.Ne_0 hd0 (by
              calc (a + (x - a)) % d = x % d := by congr 1; ring
              _ = a % d := hmod)
          obtain ⟨k, hk⟩ := Any_Eq_Mul.of.Mod.eq.Zero hj_mod
          have hk0 : 0 ≤ k := by
            have hxa : 0 ≤ x - a := by omega
            rw [hk] at hxa
            nlinarith [hpos]
          refine ⟨k.toNat, ?_, ?_⟩
          ·
            rw [List.mem_range]
            have hlt' : a + k * d < b := by rw [← hk]; omega
            have habs : |d| = d := abs_of_pos hpos
            simp only [hsign, habs, mul_one]
            set q := (b - a + d - 1) / d
            have hq_nonneg : 0 ≤ q := Int.ediv_nonneg (by omega) (le_of_lt hpos)
            have h_emod := Int.emod_add_mul_ediv (b - a + d - 1) d
            have hr_nonneg : 0 ≤ (b - a + d - 1) % d := Int.emod_nonneg (b - a + d - 1) (ne_of_gt hpos)
            have hr_lt : (b - a + d - 1) % d < d := Int.emod_lt_of_pos (b - a + d - 1) hpos
            have h_upper : (q - 1) * d < b - a := by linarith
            have hk_lt : k < q := by
              have hbd : k * d < b - a := by omega
              by_contra h
              push Not at h
              have hk_ge_mul : k * d ≥ q * d := by gcongr
              have hq_mul : q * d = b - a + d - 1 - (b - a + d - 1) % d := by linarith
              linarith
            exact LtToNat.of.Lt.Ge_0 hk0 (by rwa [Int.toNat_of_nonneg hq_nonneg])
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
      rw [hsign, In_Range.is.Any_Eq_AddMul, In_Range.is.Gt.Le]
      constructor
      ·
        rintro ⟨k, hk, hx⟩
        constructor
        · simp [hx, Int.add_emod]
        ·
          rw [hx]
          by_cases hba : b < a
          ·
            have habs : |d| = -d := Abs.eq.Neg.of.Lt_0 hneg
            simp only [hsign, habs] at hk
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
            · nlinarith [hk_le, h_upper, hneg]
            · nlinarith
          ·
            have hlen : (((b - a) * d.sign + |d| - 1) / |d|).toNat = 0 := by
              have habs : |d| = -d := Abs.eq.Neg.of.Lt_0 hneg
              simp only [hsign, habs]
              ring_nf
              have hlt : -1 - b + a - d < -d := by omega
              by_cases hn : 0 ≤ -1 - b + a - d
              · rw [Int.ediv_eq_zero_of_lt hn hlt, Int.toNat_zero]
              · rw [EqToNat_0.of.Lt_0 (Int.ediv_neg_of_neg_of_pos (by omega) (by omega : 0 < -d))]
            simp [hlen] at hk
      ·
        rintro ⟨hmod, ⟨hgt, hle⟩⟩
        by_cases hba : b < a
        ·
          have hj_mod : (a - x) % d = 0 :=
            Mod.eq.Zero.of.ModAdd.eq.Mod.Ne_0 hd0 (by
              calc (x + (a - x)) % d = a % d := by congr 1; ring
              _ = x % d := hmod.symm)
          obtain ⟨k, hk⟩ := Any_Eq_Mul.of.Mod.eq.Zero hj_mod
          have hk_nonpos : k ≤ 0 := by
            have hxa : 0 ≤ a - x := by omega
            rw [hk] at hxa
            nlinarith [hneg]
          refine ⟨(-k).toNat, ?_, ?_⟩
          ·
            rw [List.mem_range]
            set m := -k
            have hm0 : 0 ≤ m := by linarith
            have hm_gt : b < a + m * d := by
              calc
                b < x := hgt
                _ = a - k * d := by grind
                _ = a + (-k) * d := by ring
            have habs : |d| = -d := Abs.eq.Neg.of.Lt_0 hneg
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
            have hlen : (((b - a) * d.sign + |d| - 1) / |d|).toNat = q.toNat := by
              simp only [hsign, habs]
              ring_nf
              simp [q, hq_old]
            exact LtToNat.of.Lt.Ge_0 hm0 (by
              have hcast := (Int.toNat_of_nonneg hq_nonneg).symm
              rw [hlen, ← hcast]
              exact hm_lt)
          ·
            calc
              x = a - (a - x) := by ring
              _ = a - k * d := by rw [hk]
              _ = a + (-k) * d := by ring
              _ = a + ((-k).toNat : ℤ) * d := by rw [Int.toNat_of_nonneg (by linarith : 0 ≤ -k)]
        · omega


-- created on 2023-05-30
