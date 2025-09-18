import Lemma.Basic


@[main]
private lemma main
-- given
  (h : i < n)
  (h_n : n = n')
  (h_i : i = i') :
-- imply
  have h' : i' < n' := by simp_all
  HEq (Fin.mk i h) (Fin.mk i' h') := by
-- proof
  aesop


-- created on 2025-07-17
