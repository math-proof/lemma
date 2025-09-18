import stdlib.SEq
import Lemma.Basic


@[main]
private lemma simp
  {Vector : α → Sort v}
  {a b : Vector n}
-- given
  (h : a ≃ b) :
-- imply
  a = b := by
-- proof
  simp [SEq] at h
  assumption


@[main]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n}
  {b : Vector m}
-- given
  (h : a ≃ b) :
-- imply
  n = m := by
-- proof
  simp [SEq] at h
  exact h.left


-- created on 2025-05-31
-- updated on 2025-07-13
