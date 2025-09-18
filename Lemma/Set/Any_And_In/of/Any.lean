import Lemma.Basic


@[main]
private lemma main
  {p : α → Prop}
  {A : Set α}
-- given
  (h : ∃ x ∈ A, p x) :
-- imply
  ∃ x, p x ∧ x ∈ A := by
-- proof
  -- Decompose the existential quantifier and obtain the specific element `x` and proofs `hx` and `hp`
  let ⟨x, ⟨hx, hp⟩⟩ := h
  -- Use the same element `x` to construct the existential statement in the conclusion
  use x


-- created on 2025-04-20
