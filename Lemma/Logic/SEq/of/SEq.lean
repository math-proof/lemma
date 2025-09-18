import stdlib.SEq
import Lemma.Basic


@[main]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n}
  {b : Vector m}
-- given
  (h : a ≃ b) :
-- imply
  b ≃ a :=
-- proof
  SEq.symm h


-- created on 2025-07-25
