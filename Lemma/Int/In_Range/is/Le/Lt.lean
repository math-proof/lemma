import sympy.sets.fancysets
import Lemma.Int.EqToNat_0.of.Lt_0
open Int


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.In_Range.is.Le.Lt |
| comm | Int.Le.Lt.is.In_Range |
| mp | Int.Le.Lt.of.In_Range |
| mpr | Int.In_Range.of.Le.Lt |
-/
@[main, comm, mp, mpr]
private lemma main
  {a b x : ℤ} :
-- imply
  x ∈ Range a b 1 ↔ a ≤ x ∧ x < b := by
-- proof
  have mem_iff : x ∈ Range a b 1 ↔
      ∃ k ∈ List.range (((b - a) * sign (1 : ℤ) + |(1 : ℤ)| - 1) / |(1 : ℤ)|).toNat,
        x = a + (k : ℤ) * 1 := by
    simp [Range, List.mem_map, List.mem_range, eq_comm]
  by_cases hab : a < b
  ·
    have hlen : (((b - a) * sign (1 : ℤ) + |(1 : ℤ)| - 1) / |(1 : ℤ)|).toNat = (b - a).toNat := by
      simp only [Int.sign_one, abs_one, mul_one]
      ring_nf
      rw [Int.ediv_one (b - a), ← Int.toNat_of_nonneg (by omega : 0 ≤ b - a)]
    rw [mem_iff, hlen]
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
    have hlen : (((b - a) * sign (1 : ℤ) + |(1 : ℤ)| - 1) / |(1 : ℤ)|).toNat = 0 := by
      simp only [Int.sign_one, abs_one, mul_one]
      ring_nf
      by_cases hn : b - a < 0
      · exact EqToNat_0.of.Lt_0 (by omega : (b - a) / 1 < 0)
      · have heq : b - a = 0 := by omega
        rw [heq]
        rfl
    simp only [mem_iff, hlen, List.range_zero, List.not_mem_nil]
    grind


-- created on 2026-09-06
