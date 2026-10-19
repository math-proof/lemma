import Lemma.Int.SubSub.eq.Neg
open Int


@[path]
private lemma main
  [AddCommGroup α]
  {a b : α} :
-- imply
  a - (a + b) = -b := by
-- proof
  rw [Sub_Add.eq.SubSub]
  rw [SubSub.eq.Neg]


@[path]
private lemma Comm
  [AddCommGroup α]
  {a b : α} :
-- imply
  a - (b + a) = -b := by
-- proof
  rw [Sub_Add.eq.SubSub]
  rw [SubSub.eq.Neg.comm]


-- created on 2026-07-08
