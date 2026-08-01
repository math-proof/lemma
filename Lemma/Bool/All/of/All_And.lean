import sympy.Basic


@[main]
private lemma main
  {p q : α → Prop}
-- given
  (h : ∀ x : α, p x ∧ q x) :
-- imply
  ∀ x : α, q x := by
-- proof
  intro x
  exact (h x).right


@[main]
private lemma left
  {p q : α → Prop}
-- given
  (h : ∀ x : α, p x ∧ q x) :
-- imply
  ∀ x : α, p x := by
-- proof
  intro x
  exact (h x).left


-- created on 2018-10-01
