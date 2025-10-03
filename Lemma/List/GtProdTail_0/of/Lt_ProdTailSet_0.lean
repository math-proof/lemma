import Lemma.List.TailSet_0.eq.Tail
open List


@[main]
private lemma main
  {s : List ℕ}
  {a : ℕ}
-- given
  (h : k < (s.set 0 a).tail.prod) :
-- imply
  s.tail.prod > 0 := by
-- proof
  rw [TailSet_0.eq.Tail] at h
  linarith


-- created on 2025-07-18
