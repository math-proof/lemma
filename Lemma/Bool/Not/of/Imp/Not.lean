import sympy.Basic


@[main]
private lemma main
  {a b : Prop}
-- given
  (h₀ : ¬b)
  (h₁ : a → b) :
-- imply
  ¬a :=
-- proof
  -- Dot Notation: In Lean, dot notation allows functions to be called as if they were methods of an object. For example, if h : a → b is an implication, h.mt would be equivalent to applying mt to h.
  Function.mt h₁ h₀


-- created on 2025-04-13
