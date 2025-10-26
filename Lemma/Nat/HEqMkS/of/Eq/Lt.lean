import sympy.Basic


@[main]
private lemma main
-- given
  (h_i : i < n)
  (h : n = m) :
-- imply
  have h_i' : i < m := by rwa [h] at h_i
  HEq (⟨i, h_i⟩ : Fin n) (⟨i, h_i'⟩ : Fin m) := by
-- proof
  aesop


-- created on 2025-07-14
