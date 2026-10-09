import Lemma.Int.EqSub.is.Eq_Add
open Int


@[path]
private lemma main
  [AddGroup α]
  {x d : α}
-- given
  (h : x + d = 0) :
-- imply
  x = -d := by
-- proof
  simp [Eq_Sub.of.EqAdd h]


-- created on 2024-07-01
