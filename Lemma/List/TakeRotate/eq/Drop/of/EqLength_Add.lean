import Lemma.Nat.EqSub.of.EqAdd
import Lemma.List.TakeRotate.eq.Drop.of.GeLength
open Nat List


@[path]
private lemma main
  {s : List α}
-- given
  (h : s.length = i + j) :
-- imply
  (s.rotate i).take j = s.drop i := by
-- proof
  have h := Eq_Sub.of.EqAdd.left h.symm
  subst h
  apply TakeRotate.eq.Drop.of.GeLength
  omega


-- created on 2025-10-23
