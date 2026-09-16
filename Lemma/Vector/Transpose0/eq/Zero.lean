import sympy.vector.Basic
import Lemma.Vector.EqGet0_0
open Vector


@[main]
private lemma main
  [Zero α]
-- given
  (n m : ℕ) :
-- imply
  (0 : List.Vector (List.Vector α n) m).transpose = 0 := by
-- proof
  ext j i
  simp [List.Vector.transpose, EqGet0_0.val, EqGet0_0.fin]


-- created on 2026-09-16
