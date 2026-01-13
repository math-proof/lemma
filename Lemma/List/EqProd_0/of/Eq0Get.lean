import Lemma.List.EqProd_0.is.In0
open List


@[main]
private lemma main
  [MonoidWithZero α]
  [Nontrivial α]
  [NoZeroDivisors α]
  {s : List α}
  {d : Fin s.length}
-- given
  (h : s[d] = 0) :
-- imply
  s.prod = 0 := by
-- proof
  apply EqProd_0.of.In0
  grind


-- created on 2026-01-13
