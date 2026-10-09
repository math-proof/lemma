import sympy.Basic


@[path]
private lemma main
  [Decidable a] [Decidable b]
  {p f g k : α}
-- given
  (h : p = if a then f else if b then g else k) :
-- imply
  (a → p = f) ∧ (¬a ∧ b → p = g) ∧ (¬a ∧ ¬b → p = k) := by
-- proof
  subst h
  refine ⟨fun ha => if_pos ha, fun hab => ?_, fun hab => ?_⟩
  ·
    rw [if_neg hab.1, if_pos hab.2]
  ·
    rw [if_neg hab.1, if_neg hab.2]


-- created on 2023-04-25
