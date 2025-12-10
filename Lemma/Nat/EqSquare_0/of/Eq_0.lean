import sympy.core.power
import sympy.Basic


@[main]
private lemma main
  [MonoidWithZero α]
  {x : α}
-- given
  (h : x = 0) :
-- imply
  x² = 0 := by
-- proof
  rw [h]
  norm_num


-- created on 2025-04-06
