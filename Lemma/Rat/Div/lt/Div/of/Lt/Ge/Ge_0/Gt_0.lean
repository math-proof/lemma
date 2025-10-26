import sympy.Basic


@[main]
private lemma main
  [GroupWithZero α] [PartialOrder α] [PosMulReflectLT α] [MulPosReflectLT α]
  {a b c d : α}
-- given
  (h₀ : a < c)
  (h₁ : b ≥ d)
  (h₂ : c ≥ 0)
  (h₃ : d > 0) :
-- imply
  a / b < c / d :=
-- proof
  div_lt_div₀ h₀ h₁ h₂ h₃


-- created on 2025-03-25
