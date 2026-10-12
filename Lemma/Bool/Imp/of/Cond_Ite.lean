import sympy.Basic


@[path]
private lemma main
  [Decidable a] [Decidable b]
  {p f g k : α}
-- given
  (h : p = if a then f else if b then g else k) :
-- imply
  a → p = f := by
-- proof
  intro ha
  rw [h, ite_eq_left ha]


-- created on 2023-06-06
-- updated on 2026-10-12
