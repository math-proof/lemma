import sympy.vector.vector
import Lemma.Algebra.EqAppendTake__Drop
open Algebra


@[main]
private lemma main
-- given
  (v : List.Vector α (m + n)) :
-- imply
  (v.take m).val ++ (v.drop m).val = v.val := by
-- proof
  simp [List.Vector.take]
  simp [List.Vector.drop]
  cases v
  simp


-- created on 2025-05-09
