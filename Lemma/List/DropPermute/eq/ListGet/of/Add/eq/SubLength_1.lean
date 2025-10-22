import stdlib.List
import Lemma.Nat.EqSub.of.EqAdd
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.List.DropPermute.eq.ListGet
open Nat List


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h : i + d = s.length - 1) :
-- imply
  (s.permute i d).drop (i + d) = [s[i]] := by
-- proof
  have h := Eq_Sub.of.EqAdd.left h
  subst h
  rw [EqAdd_Sub.of.Ge (by omega)]
  apply DropPermute.eq.ListGet


-- created on 2025-10-22
