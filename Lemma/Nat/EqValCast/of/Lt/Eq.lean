import sympy.Basic


@[main]
private lemma main
-- given
  (h_n : m = n)
  (h_i : i < n) :
-- imply
  have h : Fin m = Fin n := by rw [h_n]
  cast h ⟨i, by rwa [h_n]⟩ = i := by
-- proof
  aesop


-- created on 2025-07-11
