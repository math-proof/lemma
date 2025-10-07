import sympy.Basic


@[main]
private lemma main
  {a b : Prop} :
-- imply
  a ∨ b ↔ a ∧ b ∨ a ∨ b := by
-- proof
    -- Apply the constructor tactic to split the equivalence into two implications.
  constructor <;> intro h
  ·
    -- Case analysis on the disjunction h : a ∨ b
    cases h with
    | inl h =>
      -- If h is of the form inl h, then h : a
      -- We need to show a ∧ b ∨ a ∨ b, which can be done by providing the left disjunct a ∧ b
      exact Or.inr (Or.inl h)
    | inr h =>
      -- If h is of the form inr h, then h : b
      -- We need to show a ∧ b ∨ a ∨ b, which can be done by providing the right disjunct b
      exact Or.inr (Or.inr h)
  ·
    -- Case analysis on the disjunction h : a ∧ b ∨ a ∨ b
    cases h with
    | inl h =>
      -- If h is of the form inl h, then h : a ∧ b
      -- We need to show a ∨ b, which can be done by providing the left disjunct a
      exact Or.inl h.left
    | inr h =>
      -- If h is of the form inr h, then h : a ∨ b
      -- We need to show a ∨ b, which is directly given by h
      exact h


-- created on 2025-04-28
