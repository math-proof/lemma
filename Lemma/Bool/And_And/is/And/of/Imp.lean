import sympy.Basic


@[main]
private lemma main
  {A C : Prop}
-- given
  (h : A → C)
  (B : Prop) :
-- imply
  A ∧ B ∧ C ↔ A ∧ B := by
-- proof
  -- Construct the equivalence by proving both directions
  constructor <;> intro h'
  -- Forward direction: A ∧ B ∧ C → A ∧ B
  -- Extract A and B from the conjunction A ∧ B ∧ C
  exact ⟨h'.1, h'.2.1⟩
  -- Reverse direction: A ∧ B → A ∧ B ∧ C
  -- Extract A and B from the conjunction A ∧ B and use the implication to derive C
  exact ⟨h'.1, h'.2, h h'.1⟩


-- created on 2025-04-09
