import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  Set.Ioo x (-x) ∪ Set.Ioo (-x) x = Set.Ioo (-|x|) |x| := by
-- proof
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h, Set.Ioo_eq_empty_of_le (by linarith : -x ≤ x), Set.empty_union]
  · rw [abs_of_nonpos h, neg_neg, Set.Ioo_eq_empty_of_le (by linarith : x ≤ -x), Set.union_empty]


-- created on 2026-09-27
