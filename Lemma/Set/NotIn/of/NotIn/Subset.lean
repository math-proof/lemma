import Lemma.Basic


@[main]
private lemma main
  {A B : Set α}
-- given
  (h₀ : e ∉ A)
  (h₁ : B ⊆ A) :
-- imply
  e ∉ B := by
-- proof
    -- Assume for contradiction that e ∈ B.
  intro h
    -- Since B ⊆ A, if e ∈ B, then e ∈ A.
  have h' : e ∈ A := h₁ h
    -- This contradicts the given fact that e ∉ A.
  contradiction


-- created on 2025-04-08
