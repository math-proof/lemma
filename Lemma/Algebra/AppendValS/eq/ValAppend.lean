import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
-- given
  (a : List.Vector α m)
  (b : List.Vector α n) :
-- imply
  a.val ++ b.val = (a ++ b).val := by
-- proof
  cases a
  cases b
  simp [List.Vector.append]
  simp [HAppend.hAppend]
  simp [List.Vector.append]
  simp [HAppend.hAppend]


-- created on 2025-05-10
