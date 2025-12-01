import sympy.Basic


@[main]
private lemma main
-- given
  (h_i : i < n)
  (h : n = m) :
-- imply
  have h_i' : i < m := by rwa [h] at h_i
  HEq (Fin.mk i h_i) (Fin.mk i h_i') := by
-- proof
  aesop


-- created on 2025-07-14
