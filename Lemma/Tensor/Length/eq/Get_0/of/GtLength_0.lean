import sympy.tensor.Basic
import sympy.Basic


@[main, comm]
private lemma main
-- given
  (h : s.length > 0)
  (X : Tensor α s) :
-- imply
  X.length = s[0] := by
-- proof
  simp [Tensor.length]
  cases s
  ·
    contradiction
  ·
    cases X
    simp


-- created on 2025-06-14
-- updated on 2025-06-15
