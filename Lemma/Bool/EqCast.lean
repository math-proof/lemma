import Lemma.Bool.SEq.is.Eq
open Bool


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.EqCast |
| comm | Bool.Eq_Cast |
-/
@[path, comm]
private lemma main
  {Vector : α → Sort v}
-- given
  (v : Vector n) :
-- imply
  cast rfl v = v := by
-- proof
  rfl


@[path, comm]
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
