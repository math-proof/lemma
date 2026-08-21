import sympy.Basic


@[main]
private lemma main
  [AddCommGroup α]
  {x a b c : α}
-- given
  (h : x + a = b ∨ x + a = c) :
-- imply
  x = b + -a ∨ x = c + -a := by
-- proof
  rcases h with h | h
  ·
    exact Or.inl (eq_add_neg_iff_add_eq.mpr h)
  ·
    exact Or.inr (eq_add_neg_iff_add_eq.mpr h)


-- created on 2018-11-28
-- updated on 2026-08-20
