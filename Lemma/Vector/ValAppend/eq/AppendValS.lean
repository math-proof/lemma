import sympy.vector.vector
import sympy.Basic


@[main, comm]
private lemma main
-- given
  (a : List.Vector α m)
  (b : List.Vector α n) :
-- imply
  (a ++ b).val = a.val ++ b.val := by
-- proof
  simp [HAppend.hAppend]
  cases a
  cases b
  simp [Append.append]


-- created on 2025-05-10
