import Lemma.Bool.SEq.is.EqCast.of.Eq
import Instance.Data.Vector.Functions.Part2
open Bool


@[path, cast]
private lemma main
  [Exp α]
-- given
  (h : n = n')
  (x : List.Vector α n) :
-- imply
  exp (cast (congrArg (List.Vector α) h) x) ≃ exp x := by
-- proof
  apply SEq.of.Eq_Cast.Eq
  .
    grind
  .
    assumption


-- created on 2025-11-29
