import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  {q : Prop}
  {x a b : α}
-- given
  (h₀ : q)
  (h₁ : ¬(p ∧ q))
  (h₂ : x = b) :
-- imply
  x =
    if p then
      a
    else
      b := by
-- proof
  split_ifs with h
  ·
    have h_And := And.intro h h₀
    contradiction
  ·
    assumption


-- created on 2025-03-21
