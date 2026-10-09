import sympy.Basic


@[path]
private lemma main
  {a b : α}
-- given
  (h : a = b) :
-- imply
  a = x ↔ b = x := by
-- proof
  rw [h]


@[path]
private lemma left
  {a b : α}
-- given
  (h : a = b) :
-- imply
  x = a ↔ x = b := by
-- proof
  rw [h]


-- created on 2025-05-29
