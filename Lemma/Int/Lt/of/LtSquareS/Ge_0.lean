import sympy.core.power
import sympy.Basic


@[main]
private lemma main
  [MonoidWithZero α]
  [LinearOrder α]
  [PosMulStrictMono α]
  [MulPosMono α]
  {a b : α}
-- given
  (h₀ : a² < b²)
  (h₁ : b ≥ 0) :
-- imply
  a < b :=
-- proof
  lt_of_pow_lt_pow_left₀ 2 (by grind) (by grind)


-- created on 2025-04-06
