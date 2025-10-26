import Lemma.Int.SubNeg
open Int


@[main]
private lemma main
  [AddCommGroup α]
  {a b : α} :
-- imply
  -a - b + a = -b := by
-- proof
  rw [SubNeg.comm]
  aesop


-- created on 2025-09-30
