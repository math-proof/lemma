import Lemma.Int.EqNeg0'0
open Int


@[main]
private lemma main
  [AddGroup α]
  {a : α}
-- given
  (h : a = 0) :
-- imply
  -a = 0 :=
-- proof
  h.symm ▸ Int.EqNeg0'0


-- created on 2025-04-19
