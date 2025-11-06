import sympy.Basic
import sympy.tensor.Basic


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : s = s')
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  (cast (congrArg (Tensor α) h) X).permuteHead n = cast (by rw [h]) (X.permuteHead n) := by
-- proof
  subst h
  rfl


-- created on 2025-10-26
