import Lemma.Nat.Odd.is.Any_Eq_AddMul2
import Lemma.Set.In_Icc.is.Le.Le
open Set Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In_Icc.Odd.is.In_SetOf_In_IccDiv_2 |
| comm | Set.In_SetOf_In_IccDiv_2.is.In_Icc.Odd |
| mp | Set.In_SetOf_In_IccDiv_2.of.In_Icc.Odd |
| mpr | Set.In_Icc.Odd.of.In_SetOf_In_IccDiv_2 |
-/
@[main, comm, mp, mpr]
private lemma main
  {a b n : ℤ} :
-- imply
  (n ∈ Icc a b ∧ n is odd) ↔
    n ∈ {2 * k + 1 | k ∈ Icc (a / 2) ((b - 1) / 2)} := by
-- proof
  constructor
  · intro ⟨h₁, h⟩
    obtain ⟨k, hk⟩ := Any_Eq_AddMul2.of.Odd h
    rw [Set.mem_setOf]
    refine ⟨k, ?_, hk.symm⟩
    rcases (In_Icc.is.Le.Le _ _).mp h₁ with ⟨ha, hb⟩
    apply In_Icc.of.Le.Le
    · rw [Int.ediv_le_iff_le_mul (by norm_num : (0 : ℤ) < 2)]
      grind
    · rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)]
      grind
  · intro h
    rw [Set.mem_setOf] at h
    obtain ⟨k, hk_icc, hk_eq⟩ := h
    constructor
    · rw [← hk_eq]
      rcases (In_Icc.is.Le.Le _ _).mp hk_icc with ⟨ha, hb⟩
      apply In_Icc.of.Le.Le
      · rw [Int.ediv_le_iff_le_mul (by norm_num : (0 : ℤ) < 2)] at ha
        grind
      · rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)] at hb
        grind
    · exact Odd.of.Any_Eq_AddMul2 ⟨k, hk_eq.symm⟩


-- created on 2018-05-29
-- updated on 2026-08-06
