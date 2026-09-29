import sympy.Basic


@[main]
private lemma main
  {A : Set α}
  {s : Set β}
  {f : α → β}
  [Decidable (∀ x ∈ A, f x ∈ s)]
-- given
  (h : ∀ x ∈ A, f x ∈ s) :
-- imply
  Bool.toNat (∀ x ∈ A, f x ∈ s) = 1 := by
-- proof
  rw [decide_eq_true h, Bool.toNat_true]


-- created on 2026-09-27
