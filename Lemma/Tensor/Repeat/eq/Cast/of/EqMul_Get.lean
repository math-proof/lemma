import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.SEqRepeat.of.EqMul_Get
open Tensor Bool


@[main]
private lemma main
  {s : List ℕ}
  {d : Fin s.length}
-- given
  (h : n * s[d] = s[d])
  (X : Tensor α s) :
-- imply
  X.repeat n d = cast (by simp_all) X := by
-- proof
  apply Eq_Cast.of.SEq
  apply SEqRepeat.of.EqMul_Get h


-- created on 2026-01-13
