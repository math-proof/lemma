import Lemma.Bool.All_Or.of.All
open Bool


@[path]
private lemma given
  {A : Set α}
  {p q : α → Prop}
-- given
  (_h₀ : ∀ x ∈ A, p x)
  (h₁ : ∀ x ∈ A, q x) :
-- imply
  ∀ x ∈ A, p x ∨ q x :=
-- proof
  All_Or.of.All.given h₁


-- created on 2019-02-06
