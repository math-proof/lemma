import sympy.Basic


@[main]
private lemma main
  {P Q : α → Prop}
  (n : α)
-- given
  (h : ∀ k, P k → Q k) :
-- imply
  P n → Q n :=
-- proof
  h n


-- created on 2026-09-26
