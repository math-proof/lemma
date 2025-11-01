import sympy.Basic
import sympy.tensor.tensor


@[main]
private lemma main
  [Add α] [Zero α]
-- given
  (h : s.length > 0)
  (X : Tensor α (s₀ :: s)) :
-- imply
  (X.sum 0).length = s[0] := by
-- proof
  apply Tensor.Length.eq.Get_0.of.GtLength_0 h


-- created on 2025-11-01
