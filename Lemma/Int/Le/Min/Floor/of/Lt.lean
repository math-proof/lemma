import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {di i0 r l s : ℤ}
-- given
  (hr : r > 0)
  (h : i0 + di * r < min (l * r + i0) s) :
-- imply
  di ≤ min (-1 / r + l) ((s - i0 - 1) / r) := by
-- proof
  have h₁ := lt_of_lt_of_le h (min_le_left _ _)
  have h₂ := lt_of_lt_of_le h (min_le_right _ _)
  have e₁ : -1 ≤ -1 / r := (Int.le_ediv_iff_mul_le hr).mpr (by linarith)
  have e₂ : -1 / r < 0 := (Int.ediv_lt_iff_lt_mul hr).mpr (by linarith)
  have hl : di < l := lt_of_mul_lt_mul_right (by linarith : di * r < l * r) hr.le
  apply le_min
  · omega
  · exact (Int.le_ediv_iff_mul_le hr).mpr (by linarith)


-- created on 2019-12-29
