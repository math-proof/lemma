import Lemma.Logic.SEq.of.Eq
open Logic


@[main, comm]
private lemma main
  {Vector : α → Sort v}
-- given
  (v : Vector n) :
-- imply
  cast rfl v = v := by
-- proof
  rfl


@[main, comm]
private lemma Rfl
  {Vector : α → Sort v}
-- given
  (v : Vector n) :
-- imply
  cast rfl v ≃ v := by
-- proof
  apply SEq.of.Eq
  apply main


-- created on 2025-07-08
