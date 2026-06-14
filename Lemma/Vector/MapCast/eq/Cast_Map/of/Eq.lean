import Lemma.Bool.EqCast.of.SEq
import Lemma.Vector.Map.as.MapCast.of.Eq
open Bool Vector


@[main]
private lemma main
-- given
  (h : n = n')
  (v : List.Vector α n)
  (f : α → β) :
-- imply
  (cast (congrArg (List.Vector α) h) v).map f = cast (congrArg (List.Vector β) h) (v.map f) := by
-- proof
  apply Eq_Cast.of.SEq
  apply MapCast.as.Map.of.Eq h.symm


-- created on 2025-11-11
