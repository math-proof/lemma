import Lemma.Bool.Imp_And.of.Imp


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
  h_a.symm.trans h_b


@[main]
private lemma subst.rhs
  {a b : α}
  {l : β}
  {r : α → β}
-- given
  (h₀ : a = b)
  (h₁ : l = r a) :
-- imply
  l = r b := by
-- proof
  rw [← h₀]
  exact h₁


@[main]
private lemma subst.lhs
  {a b : α}
  {l : α → β}
  {r : β}
-- given
  (h₀ : a = b)
  (h₁ : l a = r) :
-- imply
  l b = r := by
-- proof
  rw [← h₀]
  exact h₁


-- created on 2018-01-09
-- updated on 2026-09-27
