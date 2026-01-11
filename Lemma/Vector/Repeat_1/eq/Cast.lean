import Lemma.Bool.EqCast.of.SEq
import Lemma.Vector.SEqRepeat_1
open Bool Vector


@[main]
private lemma main
-- given
  (x : List.Vector α n) :
-- imply
  x.repeat 1 = cast (by simp) x := by
-- proof
  apply Eq_Cast.of.SEq
  apply SEqRepeat_1


-- created on 2026-01-10
