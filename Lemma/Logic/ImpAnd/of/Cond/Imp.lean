import Lemma.Basic


@[main]
private lemma main
  {q : Prop}
-- given
  (r : Prop)
  (h₁ : p → q) :
-- imply
  r ∧ p → q := by
-- proof
  intro h
  exact h₁ h.right


-- created on 2025-07-20
