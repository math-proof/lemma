import sympy.Basic


@[main]
private lemma main
  {p : α → Prop}
  {q : β → Prop}
  {A : Set α}
  {B : Set β}
-- given
  (h : ∃ x ∈ A, ∃ y ∈ B, p x ∧ q y) :
-- imply
  ∃ x y, p x ∧ q y ∧ x ∈ A ∧ y ∈ B := by
-- proof
  -- Decompose the hypothesis into components: x, y, their set memberships, and predicates
  let ⟨x, hxA, ⟨y, hyB, ⟨hp, hq⟩⟩⟩ := h
  -- Use x and y to construct the conclusion
  use x, y


-- created on 2025-04-20
