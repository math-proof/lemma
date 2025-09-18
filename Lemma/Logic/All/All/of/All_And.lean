import Lemma.Basic


@[main]
private lemma main
  {A : Set α}
  {f g : α → Prop}
-- given
  (h : ∀ x ∈ A, f x ∧ g x) :
-- imply
  ∀ x ∈ A, f x ∧ ∀ x ∈ A, g x := by
-- proof
  simp_all


-- created on 2025-07-29
