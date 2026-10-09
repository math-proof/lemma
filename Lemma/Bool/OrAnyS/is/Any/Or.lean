import Lemma.Bool.Or.is.Any_Or
open Bool


@[path]
private lemma main
  {A : Set α}
  {f g : α → Prop} :
-- imply
  (∃ x ∈ A, g x) ∨ (∃ x ∈ A, f x) ↔ ∃ x ∈ A, g x ∨ f x :=
-- proof
  Or.is.Any_Or


-- created on 2023-07-01
