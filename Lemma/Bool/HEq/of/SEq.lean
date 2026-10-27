import Theorem.Logic.SEq
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n}
  {b : Vector m}
-- given
  (h : a ≃ b) :
-- imply
  HEq a b := by
-- proof
  simp [SEq] at h
  aesop


-- created on 2025-05-31
