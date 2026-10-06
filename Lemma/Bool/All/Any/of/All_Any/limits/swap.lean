import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {B : Set β}
  {f : α → γ}
  {g : β → γ} :
-- imply
  (∀ x ∈ A, ∃ y ∈ B, f x = g y) ↔ (∀ y ∈ A, ∃ x ∈ B, f y = g x) :=
-- proof
  Iff.rfl


-- created on 2021-09-19
