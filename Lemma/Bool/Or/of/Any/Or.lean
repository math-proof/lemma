import Lemma.Bool.Or.is.Any_Or
open Bool


@[main]
private lemma given
  {A : Set α}
  {f g : α → Prop}
-- given
  (h : ∃ x ∈ A, g x ∨ f x) :
-- imply
  (∃ x ∈ A, g x) ∨ ∃ x ∈ A, f x :=
-- proof
  Or.is.Any_Or.mpr h


-- created on 2026-09-27
