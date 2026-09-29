import Lemma.Bool.Or.is.Any_Or
open Bool


@[main]
private lemma main
  {A : Set α}
  {f g : α → Prop} :
-- imply
  (∃ x ∈ A, g x) ∨ (∃ x ∈ A, f x) ↔ ∃ x ∈ A, g x ∨ f x :=
-- proof
  Or.is.Any_Or


-- created on 2026-09-27
