import sympy.Basic


@[path]
private lemma main
  [LinearOrder α]
  {x y a b : α}
-- given
  (h₀ : x > a)
  (h₁ : y > b) :
-- imply
  min x y > min a b :=
-- proof
  lt_min (lt_of_le_of_lt (min_le_left a b) h₀) (lt_of_le_of_lt (min_le_right a b) h₁)


-- created on 2019-07-18
