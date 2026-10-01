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


@[main]
private lemma single_variable
  {p q : α → Prop}
-- given
  (h : ∀ x, p x → q x) :
-- imply
  ∀ x, p x → q x :=
-- proof
  h


@[main]
private lemma Comm
  {p q : α → Prop}
-- given
  (h : ∀ n, q n → p n) :
-- imply
  ∀ n, q n → p n :=
-- proof
  h


-- created on 2026-09-26
-- updated on 2026-09-27
