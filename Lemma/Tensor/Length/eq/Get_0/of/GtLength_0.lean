import sympy.tensor.Basic
import Lemma.Basic


@[main, comm]
private lemma main
-- given
  (h : s.length > 0)
  (t : Tensor α s) :
-- imply
  t.length = s[0] := by
-- proof
  simp [Tensor.length]
  cases s
  ·
    contradiction
  ·
    cases t
    simp


-- created on 2025-06-14
-- updated on 2025-06-15
