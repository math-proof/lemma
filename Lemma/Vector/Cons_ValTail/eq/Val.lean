import Lemma.Vector.EqCons_Tail
import Lemma.Vector.Head.eq.Get_0
open Vector


@[main, comm]
private lemma main
-- given
  (s : List.Vector α (.succ n)) :
-- imply
  s[0] :: s.tail.val = s.val := by
-- proof
  simpa using congrArg Subtype.val (EqCons_Tail s)


@[main, comm]
private lemma head
-- given
  (s : List.Vector α (.succ n)) :
-- imply
  s.head :: s.tail.val = s.val := by
-- proof
  rw [Head.eq.Get_0]
  apply main


-- created on 2026-07-15
