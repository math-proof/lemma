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
  refine ⟨fun ha => ite_eq_left ha, fun hab => ?_, fun hab => ?_⟩
  ·
    rw [ite_eq_right hab.1, ite_eq_left hab.2]
  ·
    rw [ite_eq_right hab.1, ite_eq_right hab.2]


-- created on 2023-04-25
-- updated on 2026-10-12
