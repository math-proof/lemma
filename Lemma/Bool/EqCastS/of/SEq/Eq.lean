import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
open Bool


@[main]
private lemma left
  {Vector : α → Sort v}
  {a : Vector n_a}
  {b : Vector n_b}
-- given
  (h_a : n_a = n_a')
  (h : a ≃ b) :
-- imply
  cast (congrArg Vector h_a) a = cast (congrArg Vector (h.left.symm.trans h_a)) b := by
-- proof
  apply Eq.of.SEq
  apply SEqCastS.of.SEq.Eq.Eq h_a (h.left.symm.trans h_a) h


@[main]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n_a}
  {b : Vector n_b}
-- given
  (h_b : n_b = n_b')
  (h : a ≃ b) :
-- imply
  cast (congrArg Vector (h.left.trans h_b)) a = cast (congrArg Vector h_b) b := by
-- proof
  apply Eq.of.SEq
  apply SEqCastS.of.SEq.Eq.Eq (h.left.trans h_b) h_b h


-- created on 2026-07-30
