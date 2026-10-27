import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y z : ℝ}
-- given
  (h₀ : x > z)
  (h₁ : z ≥ y) :
-- imply
  x > y :=
-- proof
  lt_of_le_of_lt h₁ h₀


-- created on 2018-03-26
