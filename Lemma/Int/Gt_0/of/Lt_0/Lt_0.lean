import sympy.Basic


@[main]
private lemma main
  [Semiring α]
  [PartialOrder α]
  [ExistsAddOfLE α]
  [MulPosStrictMono α]
  [AddRightStrictMono α]
  [AddRightReflectLT α]
  {x y : α}
-- given
  (h₀ : x < 0)
  (h₁ : y < 0) :
-- imply
  x * y > 0 :=
-- proof
  mul_pos_of_neg_of_neg h₀ h₁


-- created on 2025-03-23
