import sympy.Basic


@[main]
private lemma main
  [LinearOrder α]
  {x y a b : α}
-- given
  (h₀ : x ≤ a)
  (h₁ : y ≤ b) :
-- imply
  min x y ≤ min a b :=
-- proof
  min_le_min h₀ h₁


-- created on 2019-11-20
