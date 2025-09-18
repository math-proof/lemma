import Lemma.Logic.Imp_And.of.Imp


@[main]
private lemma subst
  {a b : α}
  {p q : α → β}
-- given
  (h₀ : a = b)
  (h₁ : p a = q a) :
-- imply
  p b = q b := by
-- proof
  exact h₀ ▸ h₁


@[main]
private lemma main
  {a b : α}
  {f : α → α → α}
-- given
  (h_a : f a b = a)
  (h_b : f a b = b) :
-- imply
  a = b :=
-- proof
  Eq.trans h_a.symm h_b


-- created on 2025-06-06
