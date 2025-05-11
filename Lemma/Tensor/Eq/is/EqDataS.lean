import sympy.tensor.tensor
import Lemma.Basic


@[main]
private lemma main
  [Inhabited α]
  {a b : Tensor α s} :
-- imply
  a = b ↔ a.data = b.data := by
-- proof
  cases a
  cases b
  simp


-- created on 2025-05-06
