import sympy.tensor.tensor


@[main]
private lemma main
  [Mul α]
-- given
  (A B : Tensor α s)
  (d : ℕ) :
-- imply
  (A * B).permuteHead d = A.permuteHead d * B.permuteHead d := by
-- proof
  sorry


-- created on 2025-12-02
