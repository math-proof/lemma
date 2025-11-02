import sympy.tensor.Basic


@[main]
private lemma main
-- given
  (X : Tensor α [m, n].tail.tail) :
-- imply
  X = cast (congrArg (Tensor α) (by simp)) ⟨X.data⟩ := by
-- proof
  aesop


-- created on 2025-07-19
