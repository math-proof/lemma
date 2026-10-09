import Lemma.Bool.Any.Or.Distributed.of.Or
import Lemma.Bool.Any.Cond.of.Cond
open Bool


@[path]
private lemma main
  {A : Set α}
  {f g : α → Prop}
-- given
  (h₀ : A.Nonempty)
  (h₁ : (∃ x ∈ A, g x) ∨ ∀ x, f x) :
-- imply
  ∃ x ∈ A, g x ∨ f x := by
-- proof
  rcases h₁ with h | h
  ·
    exact Any.Or.Distributed.of.Or (Or.inl h)
  ·
    exact Any.Or.Distributed.of.Or (Or.inr (Any.Cond.of.Cond h₀ h))


-- created on 2020-02-19
