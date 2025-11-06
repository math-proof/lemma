import sympy.tensor.Basic
import sympy.Basic


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s = s')
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (cast (congrArg (Tensor α) h) X).permuteTail n = cast (by rw [h]) (X.permuteTail n) := by
-- proof
  subst h
  rfl


-- created on 2025-10-18
