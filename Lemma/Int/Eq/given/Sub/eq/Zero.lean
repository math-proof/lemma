import Lemma.Int.Sub.eq.Zero.is.Eq
open Int


@[main]
private lemma main
  [AddGroup α]
  (a b : α)
-- given
  (h : a = b) :
-- imply
  a - b = 0 := by
-- proof
  exact Sub.eq.Zero.of.Eq h


-- created on 2026-10-03
