import stdlib.List.Vector
import Lemma.Logic.EqCast.of.SEq
open Logic


@[main]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
  {v : List.Vector α s.prod}
  {v' : List.Vector α ((s.take d).prod * (s.drop d).prod)}
-- given
  (h : v' ≃ v) :
-- imply
  v'.unflatten = v.splitAt d := by
-- proof
  unfold List.Vector.splitAt
  simp
  congr
  apply Eq_Cast.of.SEq
  assumption


-- created on 2025-07-08
