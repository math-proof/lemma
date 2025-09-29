import sympy.Basic


@[main]
private lemma main
  {i : Fin n}
-- given
  (h : i.val = n - 1) :
-- imply
  i = ⟨n - 1, by linarith [i.isLt]⟩ := by
-- proof
  aesop


-- created on 2025-06-17
