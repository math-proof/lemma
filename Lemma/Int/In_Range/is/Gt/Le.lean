import sympy.sets.fancysets
import Lemma.Int.EqToNat_0.of.Lt_0
import Lemma.Int.Sign.eq.Neg1.of.Lt_0
open Int


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.In_Range.is.Gt.Le |
| comm | Int.Gt.Le.is.In_Range |
| mp | Int.Gt.Le.of.In_Range |
| mpr | Int.In_Range.of.Gt.Le |
-/
@[main, comm, mp, mpr]
private lemma main
  {a b x : ℤ} :
-- imply
  x ∈ Range a b (-1) ↔ b < x ∧ x ≤ a := by
-- proof
  have mem_iff : x ∈ Range a b (-1) ↔
      ∃ k ∈ List.range (((b - a) * sign (-1 : ℤ) + |(-1 : ℤ)| - 1) / |(-1 : ℤ)|).toNat,
        x = a + (k : ℤ) * (-1) := by
    simp [Range, List.mem_map, List.mem_range, eq_comm]
  by_cases hba : b < a
  ·
    have hlen : (((b - a) * sign (-1 : ℤ) + |(-1 : ℤ)| - 1) / |(-1 : ℤ)|).toNat = (a - b).toNat := by
      simp only [Sign.eq.Neg1.of.Lt_0 (by omega : (-1 : ℤ) < 0), abs_neg]
      ring_nf
      rw [Int.ediv_one (-b + a), show -b + a = a - b by abel]
    rw [mem_iff, hlen]
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
    have hlen : (((b - a) * sign (-1 : ℤ) + |(-1 : ℤ)| - 1) / |(-1 : ℤ)|).toNat = 0 := by
      simp only [Sign.eq.Neg1.of.Lt_0 (by omega : (-1 : ℤ) < 0), abs_neg]
      ring_nf
      by_cases hn : a - b < 0
      · exact EqToNat_0.of.Lt_0 (by omega : (-b + a) / 1 < 0)
      · have heq : a - b = 0 := by omega
        have h0 : -b + a = 0 := by linarith [heq]
        rw [h0]
        rfl
    simp only [mem_iff, hlen, List.range_zero, List.not_mem_nil]
    grind


-- created on 2026-09-06
