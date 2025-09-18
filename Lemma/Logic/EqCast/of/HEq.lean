import Lemma.Logic.Eq.of.HEq
import Lemma.Logic.HEq.is.EqCast.of.Eq
open Logic


@[main, comm 1]
private lemma main
  {a : α}
  {b : β}
-- given
  (h : HEq a b) :
-- imply
  cast (Eq.of.HEq h) a = b :=
-- proof
  EqCast.of.HEq.Eq (Eq.of.HEq h) h


-- created on 2025-07-16
