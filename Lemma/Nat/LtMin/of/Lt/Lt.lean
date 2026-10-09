import sympy.Basic


@[path]
private lemma main
  [LinearOrder α]
  {x y a b : α}
-- given
  (h₀ : x < a)
  (h₁ : y < b) :
-- imply
  min x y < min a b :=
-- proof
  lt_min (lt_of_le_of_lt (min_le_left x y) h₀) (lt_of_le_of_lt (min_le_right x y) h₁)


@[path]
private lemma both
  [LinearOrder α]
  {x y a b : α}
-- given
  (h₀ : x < y)
  (h₁ : a < b) :
-- imply
  min x a < min y b :=
-- proof
  lt_min (lt_of_le_of_lt (min_le_left x a) h₀) (lt_of_le_of_lt (min_le_right x a) h₁)


-- created on 2019-05-12
