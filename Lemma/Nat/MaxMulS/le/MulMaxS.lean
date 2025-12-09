import sympy.Basic


/--
the triangular inequality for `max` and `*`
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
  a * b ⊔ c * d ≤ (a ⊔ c) * (b ⊔ d) :=
-- proof
  max_mul_mul_le_max_mul_max'


-- created on 2025-12-08
