import sympy.Basic


@[path]
private lemma main
  [Decidable a] [Decidable b]
  {p f g k : α} :
-- imply
  (p = if a then f else if b then g else k) ↔ (a → p = f) ∧ (¬a ∧ b → p = g) ∧ (¬a ∧ ¬b → p = k) := by
-- proof
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]


-- created on 2023-04-25
