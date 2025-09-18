import Lemma.Basic


@[main]
private lemma main
  [MonoidWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulStrictMono α]
  [MulPosStrictMono α]
  {x : α}
-- given
  (h₀ : x > 1)
  (h₁ : n < m) :
-- imply
  x ^ n < x ^ m :=
-- proof
  pow_lt_pow_right₀ h₀ h₁


-- created on 2025-05-23
