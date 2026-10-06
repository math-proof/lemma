import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b d : ℤ}
-- given
  (h : d * x ∉ Set.Ico a (b + 1))
  (hd : d > 0) :
-- imply
  x ∉ Set.Ico ((a + d - 1) / d) (b / d + 1) := by
-- proof
  intro hmem
  obtain ⟨h₁, h₂⟩ := hmem
  rw [Int.ediv_le_iff_le_mul hd] at h₁
  rw [Int.lt_add_one_iff, Int.le_ediv_iff_mul_le hd] at h₂
  apply h
  rw [Set.mem_Ico, mul_comm d x]
  constructor <;> omega


-- created on 2021-06-08
