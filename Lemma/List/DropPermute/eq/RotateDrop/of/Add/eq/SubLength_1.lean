import stdlib.List
import Lemma.Nat.EqSub.of.EqAdd
import Lemma.List.DropPermute.eq.RotateDrop
open Nat List


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h : i + d = s.length - 1) :
-- imply
  (s.permute i ↑(d)).drop i = (s.drop i).rotate 1 := by
-- proof
  have h_d := Eq_Sub.of.EqAdd.left h
  subst h_d
  apply DropPermute.eq.RotateDrop


-- created on 2025-10-22
