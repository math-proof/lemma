import Lemma.Nat.Odd.is.Any_Eq_AddMul2
import Lemma.Set.In_Icc.is.Le.Le
open Set Int Nat


@[main]
private lemma main
  {a b n : ℤ}
-- given
  (h : n is odd)
  (h₁ : n ∈ Icc a b) :
-- imply
  n ∈ {2 * k + 1 | k ∈ Icc (a / 2) ((b - 1) / 2)} := by
-- proof
  obtain ⟨k, hk⟩ := Any_Eq_AddMul2.of.Odd h
  rw [Set.mem_setOf]
  refine ⟨k, ?_, hk.symm⟩
  rcases (In_Icc.is.Le.Le _ _).mp h₁ with ⟨ha, hb⟩
  apply In_Icc.of.Le.Le
  · rw [Int.ediv_le_iff_le_mul (by norm_num : (0 : ℤ) < 2)]
    grind
  · rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 2)]
    grind


-- created on 2018-05-29
