import Lemma.Basic


@[main]
private lemma main
  [Decidable p]
  {R : α → β → Prop}
  {a b : α}
-- given
  (h₁ : R a c ∧ p) :
-- imply
  R (if p then
    a
  else
    b) c ∧ p := by
-- proof
  simp_all


-- created on 2025-07-29
