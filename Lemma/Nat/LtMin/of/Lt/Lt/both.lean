import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x y a b : α}
-- given
  (h₀ : x < y)
  (h₁ : a < b) :
-- imply
  min x a < min y b := by
-- proof
  exact lt_min (lt_of_le_of_lt (min_le_left x a) h₀) (lt_of_le_of_lt (min_le_right x a) h₁)


-- created on 2019-05-12
