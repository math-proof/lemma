import sympy.Basic


@[main, comm]
private lemma main
-- given
  (h_n : m = n)
  (i : Fin n) :
-- imply
  have h : Fin m = Fin n := by rw [h_n]
  cast h ⟨i, by simp_all⟩ = i := by
-- proof
  aesop


-- created on 2025-05-23
-- updated on 2025-05-31
