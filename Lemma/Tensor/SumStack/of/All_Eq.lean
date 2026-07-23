import sympy.tensor.stack


@[main]
private lemma main
  [Add α] [Zero α]
  {X Y : Fin n → Tensor α s}
-- given
  (h : ∀ i : Fin n, X i = Y i) :
-- imply
  ∑ i < n, X i = ∑ i < n, Y i := by
-- proof
  aesop


-- created on 2026-07-22
