import sympy.Basic


@[main]
private lemma main
-- given
  (a : α)
  (l : ℕ) :
-- imply
  (List.replicate l a).length = l := by
-- proof
  simp


-- created on 2025-05-02
