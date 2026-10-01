import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x y a b : α}
-- given
  (h₀ : x < a)
  (h₁ : y < b) :
-- imply
  max x y < max a b :=
-- proof
  max_lt (lt_max_of_lt_left h₀) (lt_max_of_lt_right h₁)


-- created on 2026-09-27
