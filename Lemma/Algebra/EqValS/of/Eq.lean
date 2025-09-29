import stdlib.SEq
import stdlib.List.Vector
import sympy.Basic


@[main]
private lemma main
  {a : List.Vector α n}
  {b : List.Vector α m}
-- given
  (h : a ≃ b) :
-- imply
  a.val = b.val := by
-- proof
  simp [SEq] at h
  aesop


-- created on 2025-05-23
