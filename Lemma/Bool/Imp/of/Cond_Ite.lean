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
  rw [h, if_pos ha]


-- created on 2023-06-06
