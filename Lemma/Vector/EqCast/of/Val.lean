import Lemma.Vector.Eq.of.Val
open Vector


@[main, comm 1]
private lemma main
  {a : List.Vector α n}
  {b : List.Vector α m}
-- given
  (h_eq : a.val = b.val) :
-- imply
  cast (congrArg (List.Vector α ) (Eq.of.Val.nat h_eq)) a = b := by
-- proof
  have h_n := Eq.of.Val.nat h_eq
  subst h_n
  apply Eq.of.Val
  simpa using h_eq


-- created on 2025-05-23
-- updated on 2026-08-24
