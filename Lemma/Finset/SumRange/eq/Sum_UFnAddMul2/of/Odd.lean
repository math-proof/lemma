import sympy.sets.fancysets
import Lemma.Finset.SumSetOf_Odd.eq.Sum_UFnAddMul2
import Lemma.Int.In_Range.is.Mod.In_Range
import Lemma.Int.EqSign_1.of.Gt_0
import Lemma.Int.EqToNat_0.of.Lt_0
import Lemma.Nat.Odd.is.Mod_2.eq.One
open Finset Nat Int


@[main]
private lemma main
  [AddCommMonoid α]
  {a : ℤ}
-- given
  (h : a is odd)
  (b : ℤ)
  (f : ℤ → α) :
-- imply
  ∑ n ∈ (Range a b 2).toFinset, f n = ∑ n ∈ Finset.Ico (a / 2) (b / 2), f (2 * n + 1) := by
-- proof
  have h1 : a % 2 = 1 := Mod_2.eq.One.of.Odd h
  have h_sign : sign (2 : ℤ) = 1 := EqSign_1.of.Gt_0 (by decide)
  have h_range1 : ∀ x : ℤ, x ∈ Range a b 1 ↔ a ≤ x ∧ x < b := by
    intro x
    have hx : x ∈ Range a b 1 ↔
        ∃ k ∈ List.range (((b - a) * sign (1 : ℤ) + |(1 : ℤ)| - 1) / |(1 : ℤ)|).toNat,
          x = a + (k : ℤ) * 1 := by
      simp [Range, List.mem_map, List.mem_range, eq_comm]
    have hlen : (((b - a) * sign (1 : ℤ) + |(1 : ℤ)| - 1) / |(1 : ℤ)|).toNat = (b - a).toNat := by
      simp [Int.sign_one, abs_one, mul_one]
    rw [hx, hlen]
    constructor
    ·
      rintro ⟨k, hk, rfl⟩
      have hk' := List.mem_range.mp hk
      constructor
      ·
        omega
      ·
        have : (k : ℤ) < (b - a).toNat := Nat.cast_lt.mpr hk'
        if hba : 0 ≤ b - a then
          rw [Int.toNat_of_nonneg hba] at this
          omega
        else
          rw [EqToNat_0.of.Lt_0 (by omega : b - a < 0)] at this
          omega
    ·
      intro ⟨hle, hlt⟩
      refine ⟨(x - a).toNat, List.mem_range.mpr ?_, ?_⟩
      ·
        exact (Int.toNat_lt (by omega : 0 ≤ x - a)).mpr (by omega)
      ·
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ x - a)]
        ring
  have h_fin : (Range a b 2).toFinset = {n ∈ Finset.Ico a b | n % 2 = 1} := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_Ico]
    constructor
    ·
      intro hx
      have hx' := Mod.In_Range.of.In_Range (d := 2) hx
      rw [h_sign] at hx'
      obtain ⟨hmod, hx1⟩ := hx'
      exact ⟨(h_range1 x).mp hx1, by omega⟩
    ·
      intro ⟨hxIco, hmod⟩
      apply In_Range.of.Mod.In_Range (d := 2)
      ·
        omega
      ·
        rw [h_sign]
        exact (h_range1 x).mpr hxIco
  rw [h_fin, SumSetOf_Odd.eq.Sum_UFnAddMul2]


-- created on 2026-08-16
