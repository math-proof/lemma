import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ} :
-- imply
  Set.Icc a b ∪ Set.Icc b a = Set.Icc (min a b) (max b a) := by
-- proof
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left h]
    exact Set.union_eq_left.mpr fun t ht => ⟨h.trans ht.1, ht.2.trans h⟩
  · rw [min_eq_right h, max_eq_right h]
    exact Set.union_eq_right.mpr fun t ht => ⟨h.trans ht.1, ht.2.trans h⟩


-- created on 2020-06-04
