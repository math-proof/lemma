import sympy.Basic


@[main]
private lemma main
  [Fintype β] [AddCommMonoid γ]
  {n i : ℕ}
  {f : (Fin (n - i) → β) → γ} :
-- imply
  ∑ x : Fin (n - i) → β, f x = ∑ y : Fin (n - i) → β, f y :=
-- proof
  rfl


-- created on 2026-09-27
