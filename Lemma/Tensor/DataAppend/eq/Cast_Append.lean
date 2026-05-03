import sympy.Basic
import sympy.tensor.Basic


@[main]
private lemma main
-- given
  (A : Tensor α (m :: s))
  (B : Tensor α (n :: s)) :
-- imply
  (A ++ B).data = cast (by simp [right_distrib]) (A.data ++ B.data) := by
-- proof
  simp [HAppend.hAppend]


-- created on 2026-05-02
