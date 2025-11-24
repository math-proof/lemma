import Lemma.List.EqAppendDropLast.of.GtLength_0
open List


@[main, comm]
private lemma main
  [Monoid α]
  {s : List α}
-- given
  (h : s.length > 0) :
-- imply
  s.prod = s.dropLast.prod * s[s.length - 1] := by
-- proof
  have := EqAppendDropLast.of.GtLength_0 h
  have := congrArg List.prod this
  simp at this
  aesop


-- created on 2025-11-24
