import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.SEqAppend.of.Eq_0
open Tensor Bool


@[main]
private lemma cons
  {X : Tensor α (n :: s)}
  {O : Tensor α (m :: s)}
-- given
  (h : m = 0) :
-- imply
  X ++ O = cast (by simp_all) X := by
-- proof
  apply Eq_Cast.of.SEq
  apply SEqAppend.of.Eq_0.cons h


@[main]
private lemma main
  {X : Tensor α (bz ++ n :: s)}
  {O : Tensor α (bz ++ m :: s)}
-- given
  (h : m = 0) :
-- imply
  X ++ O = cast (by simp_all) X := by
-- proof
  apply Eq_Cast.of.SEq
  apply SEqAppend.of.Eq_0 h


-- created on 2026-01-13
