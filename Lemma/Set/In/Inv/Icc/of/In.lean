import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (ha : 0 < a)
  (h : x ∈ Set.Icc a b) :
-- imply
  1 / x ∈ Set.Icc (1 / b) (1 / a) := by
-- proof
  obtain ⟨hax, hxb⟩ := h
  have hx : 0 < x := lt_of_lt_of_le ha hax
  exact ⟨one_div_le_one_div_of_le hx hxb, one_div_le_one_div_of_le ha hax⟩


-- created on 2020-06-21
