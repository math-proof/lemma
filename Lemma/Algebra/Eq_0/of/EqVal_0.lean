import sympy.Basic


@[main]
private lemma main
  {i : Fin n}
-- given
  (h : i.val = 0) :
-- imply
  i = ⟨0, by linarith [i.isLt]⟩ := by
-- proof
  aesop


-- created on 2025-06-16
