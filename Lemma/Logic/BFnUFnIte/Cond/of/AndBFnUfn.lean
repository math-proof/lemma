import Lemma.Basic


@[main]
private lemma main
  [Decidable p]
  {γ : Sort u}
  {R : α → β → Prop}
  {f : γ → α}
  {a b : γ}
-- given
  (h₁ : R (f a) c ∧ p) :
-- imply
  R (f (if p then
    a
  else
    b)) c ∧ p := by
-- proof
  simp_all


-- created on 2025-07-29
