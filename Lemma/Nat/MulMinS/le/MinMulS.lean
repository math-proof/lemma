import sympy.Basic


/--
the triangular inequality for `min` and `*`
-/
@[main]
private lemma main
  [Mul α]
  [LinearOrder α]
  [MulLeftMono α]
  [MulRightMono α]
-- given
  (a b c d : α) :
-- imply
  (a ⊓ c) * (b ⊓ d) ≤ a * b ⊓ c * d :=
-- proof
  min_mul_min_le_min_mul_mul'


-- created on 2025-12-08
