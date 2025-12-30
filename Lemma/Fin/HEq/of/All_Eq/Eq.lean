import sympy.Basic


@[main]
private lemma main
  {f : Fin n → β}
  {g : Fin m → β}
-- given
  (h₀ : n = m)
  (h₁ : ∀ (i : Fin n), f i = g ⟨i, by simp_all [← h₀]⟩) :
-- imply
  HEq f g := by
-- proof
  aesop


-- created on 2025-12-30
