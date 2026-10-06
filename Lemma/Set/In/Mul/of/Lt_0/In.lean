import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {t x a b : ℝ}
-- given
  (ht : t < 0)
  (h : x ∈ Set.Ioc a b) :
-- imply
  x * t ∈ Set.Ico (b * t) (a * t) := by
-- proof
  obtain ⟨hax, hxb⟩ := h
  exact ⟨mul_le_mul_of_nonpos_right hxb ht.le, mul_lt_mul_of_neg_right hax ht⟩


-- created on 2021-06-03
-- updated on 2023-04-17
